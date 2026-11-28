import Erdos478QuadraticSquareClasses
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finite.Perm

/-!
# A nonreal cubic over a real normal field

Let a monic irreducible cubic over the rationals have negative
discriminant. It stays irreducible over every real normal extension:
one root there would force its other conjugates to be real. The
discriminant remains nonsquare, so the relative splitting degree is six.
-/

namespace Erdos478.GapReality
open Polynomial IntermediateField
noncomputable section

private theorem discriminant_square {c : Cubic ℚ} (ha : c.a≠0)
    (L : Type) [Field L] [Algebra ℚ L] (hs : (c.toPoly.map (algebraMap ℚ L)).Splits) :
    ∃ t : L, t^2=algebraMap ℚ L c.discr := by
  obtain ⟨x,y,z,h⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hs
  exact ⟨_,(Cubic.discr_eq_prod_three_roots ha h).symm⟩

private theorem negative_nonsquare (E : IntermediateField ℚ ℝ) {d : ℚ} (hd : d<0) :
    ∀ t : E, t^2≠algebraMap ℚ E d := by
  intro t ht
  have he := congrArg (fun x : E => (x:ℝ)) ht
  change (t:ℝ)^2=(d:ℝ) at he
  have hd' : (d:ℝ)<0 := by exact_mod_cast hd
  linarith [sq_nonneg (t:ℝ)]

theorem cubic_irreducible_over_real_normal (c : Cubic ℚ) (hm : c.a=1)
    (hi : Irreducible c.toPoly) (hd : c.discr<0) (E : IntermediateField ℚ ℝ) [Normal ℚ E] :
    Irreducible (c.toPoly.map (algebraMap ℚ E)) := by
  have ha : c.a≠0 := hm.trans_ne one_ne_zero
  have hmon := Cubic.monic_of_a_eq_one hm
  have hdeg := (hmon.natDegree_map (algebraMap ℚ E)).trans (Cubic.natDegree_of_a_ne_zero ha)
  apply ((hmon.map _).irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro x hx
  have hr := (mem_roots (hmon.map (algebraMap ℚ E)).ne_zero).mp hx
  have hx' : aeval x c.toPoly=0 := by simpa [IsRoot,eval_map_algebraMap] using hr
  have hmin := minpoly.eq_of_irreducible_of_monic hi hx' hmon
  have hs := (inferInstance : Normal ℚ E).splits x
  rw [← hmin] at hs
  obtain ⟨t,ht⟩ := discriminant_square ha E hs
  exact negative_nonsquare E hd t ht

theorem cubic_degree_over_real_normal (c : Cubic ℚ) (hm : c.a=1)
    (hi : Irreducible c.toPoly) (hd : c.discr<0) (E : IntermediateField ℚ ℝ) [Normal ℚ E] :
    Module.finrank E (c.toPoly.map (algebraMap ℚ E)).SplittingField=6 := by
  let F := c.toPoly.map (algebraMap ℚ E)
  let K := F.SplittingField
  have ha : c.a≠0 := hm.trans_ne one_ne_zero
  have hg : F.natDegree=3 := ((Cubic.monic_of_a_eq_one hm).natDegree_map _).trans
    (Cubic.natDegree_of_a_ne_zero ha)
  have hir : Irreducible F := cubic_irreducible_over_real_normal c hm hi hd E
  have hs : (c.toPoly.map (algebraMap ℚ K)).Splits := by
    rw [IsScalarTower.algebraMap_eq ℚ E K,← Polynomial.map_map]
    exact SplittingField.splits F
  obtain ⟨t,ht⟩ := discriminant_square ha K hs
  have ht' : t^2=algebraMap E K (algebraMap ℚ E c.discr) := by simpa using ht
  have htwo := SquareClasses.sqrt_adjoin_degree (negative_nonsquare E hd) ht'
  have heven : 2∣Module.finrank E K := by
    refine ⟨Module.finrank E⟮t⟯ K,?_⟩
    rw [← Module.finrank_mul_finrank E E⟮t⟯ K,htwo]
  have hthree := Gal.prime_degree_dvd_card hir (hg ▸ Nat.prime_three)
  rw [Gal.card_of_separable hir.separable,hg] at hthree
  let : Fact ((F.map (algebraMap E K)).Splits) := ⟨SplittingField.splits F⟩
  have H := Nat.card_le_card_of_injective _ (Gal.galActionHom_injective F K)
  rw [Nat.card_perm,Nat.card_coe_set_eq,Gal.card_of_separable hir.separable] at H
  have upper : Module.finrank E K≤6 := H.trans (Nat.factorial_le ((F.ncard_rootSet_le K).trans_eq hg))
  change 3∣Module.finrank E K at hthree
  change Module.finrank E K=6
  have := Module.finrank_pos (R:=E) (M:=K)
  omega

/-- Adjoining the roots of a monic irreducible cubic of negative
discriminant multiplies the degree of any real splitting field by six. -/
theorem cubic_compositum_degree (P : ℚ[X]) (hP : P≠0)
    (hs : (P.map (algebraMap ℚ ℝ)).Splits) (c : Cubic ℚ) (hm : c.a=1)
    (hi : Irreducible c.toPoly) (hd : c.discr<0) :
    Module.finrank ℚ (P*c.toPoly).SplittingField=Module.finrank ℚ P.SplittingField*6 := by
  let E := adjoin ℚ (P.rootSet ℝ)
  let : IsSplittingField ℚ E P := adjoin_rootSet_isSplittingField hs
  let : Normal ℚ E := Normal.of_isSplittingField P
  let : FiniteDimensional ℚ E := IsSplittingField.finiteDimensional E P
  let K := (c.toPoly.map (algebraMap ℚ E)).SplittingField
  let : IsSplittingField ℚ K (P*c.toPoly) :=
    IsSplittingField.mul (K:=E) K P c.toPoly hP hi.ne_zero
  calc
    _ = Module.finrank ℚ K := (IsSplittingField.algEquiv K (P*c.toPoly)).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℚ E*Module.finrank E K := (Module.finrank_mul_finrank ℚ E K).symm
    _ = _ := by rw [(IsSplittingField.algEquiv E P).toLinearEquiv.finrank_eq,
                  cubic_degree_over_real_normal c hm hi hd E]

#print axioms cubic_compositum_degree
#print axioms cubic_irreducible_over_real_normal
#print axioms cubic_degree_over_real_normal
end
end Erdos478.GapReality
