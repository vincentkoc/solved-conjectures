import Erdos478RootPairOrder
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Coprime-degree root fields

Over an extension of coprime degree an irreducible monic polynomial
remains irreducible. The two integral generators consequently span a
full-rank order in their composite number field.
-/

namespace Erdos478.RootPairs
noncomputable section
open Polynomial Module NumberField

theorem irreducible_map_coprime {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {g : F[X]} (hm : g.Monic) (hi : Irreducible g)
    (hc : g.natDegree.Coprime (finrank F K)) : Irreducible (g.map (algebraMap F K)) := by
  let G := g.map (algebraMap F K)
  have hG : G.Monic := hm.map _
  have hdeg : G.natDegree = g.natDegree := hm.natDegree_map _
  obtain ⟨h,hh,hir,hd⟩ := exists_monic_irreducible_factor G (not_isUnit_of_natDegree_pos _
    (hdeg ▸ hi.natDegree_pos))
  let : Fact (Irreducible h) := ⟨hir⟩
  let E := AdjoinRoot h
  let : FiniteDimensional K E := (AdjoinRoot.powerBasis hir.ne_zero).finite
  let : FiniteDimensional F E := Module.Finite.trans K E
  have hroot : aeval (AdjoinRoot.root h) g = 0 := by
    rw [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq F K E).symm,AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.mpr hd
  have hmin := minpoly.eq_of_irreducible_of_monic hi hroot hm
  have hv := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := F) (AdjoinRoot.root h))
  rw [← hmin,← finrank_mul_finrank F K E] at hv
  have hr : finrank K E = h.natDegree := (AdjoinRoot.powerBasis hir.ne_zero).finrank
  rw [hr] at hv
  have hle := Nat.le_of_dvd hir.natDegree_pos (hc.dvd_of_dvd_mul_left hv)
  have he := eq_of_monic_of_dvd_of_natDegree_le hh hG hd (hdeg ▸ hle)
  change Irreducible G
  rwa [he]

/-- Injective changes of coefficients stay injective on quotients by a monic
polynomial, by uniqueness of the remainder in monic division. -/
theorem map_injective {A B : Type*} [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (f : A[X]) (hf : f.Monic) :
    Function.Injective (AdjoinRoot.map i f (f.map i) dvd_rfl) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective z
  have he : AdjoinRoot.map i f (f.map i) dvd_rfl (AdjoinRoot.mk f P) =
      AdjoinRoot.mk (f.map i) (P.map i) := by
    rw [AdjoinRoot.map,AdjoinRoot.lift_mk,← AdjoinRoot.aeval_eq,aeval_def,eval₂_map]
    rfl
  rw [he,AdjoinRoot.mk_eq_zero] at hz
  apply AdjoinRoot.mk_eq_zero.mpr
  apply (modByMonic_eq_zero_iff_dvd hf).mp
  apply Polynomial.map_injective i hi
  rw [Polynomial.map_zero,map_modByMonic i hf]
  exact (modByMonic_eq_zero_iff_dvd (hf.map _)).mpr hz


/-- The integral root algebra embeds in the ring of integers with full additive rank. -/
theorem exists_full_order (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hi : Irreducible (f.map (algebraMap ℤ ℚ))) (hj : Irreducible (g.map (algebraMap ℤ ℚ)))
    (hc : g.natDegree.Coprime f.natDegree) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (j : pairOrder f g →+* 𝓞 K),
      Function.Injective j ∧ finrank ℤ (pairOrder f g) = finrank ℚ K := by
  classical
  let F := AdjoinRoot (f.map (algebraMap ℤ ℚ))
  let : Fact (Irreducible (f.map (algebraMap ℤ ℚ))) := ⟨hi⟩
  let : FiniteDimensional ℚ F := (AdjoinRoot.powerBasis hi.ne_zero).finite
  have hF : finrank ℚ F = f.natDegree :=
    (AdjoinRoot.powerBasis hi.ne_zero).finrank.trans (hf.natDegree_map _)
  let A := AdjoinRoot f
  let j : A →+* F := AdjoinRoot.map (algebraMap ℤ ℚ) _ _ dvd_rfl
  have hj' : Function.Injective j := map_injective _ (Int.cast_injective) _ hf
  let : Nontrivial A := j.domain_nontrivial
  let h := g.map (AdjoinRoot.of f)
  have hm : h.Monic := hg.map _
  have hG : h.map j = (g.map (algebraMap ℤ ℚ)).map (algebraMap ℚ F) := by
    simp only [h,Polynomial.map_map,RingHom.ext_int (j.comp _) ((algebraMap ℚ F).comp (algebraMap ℤ ℚ))]
  have hi' : Irreducible (h.map j) := by
    rw [hG]
    apply irreducible_map_coprime (hg.map _) hj
    rwa [hF,hg.natDegree_map]
  let K := AdjoinRoot (h.map j)
  let : Fact (Irreducible (h.map j)) := ⟨hi'⟩
  let : FiniteDimensional F K := (AdjoinRoot.powerBasis hi'.ne_zero).finite
  let : FiniteDimensional ℚ K := Module.Finite.trans F K
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let : NumberField K := { to_finiteDimensional := by infer_instance }
  let ι : pairOrder f g →+* K := AdjoinRoot.map j h _ dvd_rfl
  have hι : Function.Injective ι := map_injective _ hj' _ hm
  let : Module.Finite ℤ A := hf.finite_adjoinRoot
  let : Module.Free ℤ A := hf.free_adjoinRoot
  let : Module.Finite A (pairOrder f g) := hm.finite_adjoinRoot
  let : Module.Free A (pairOrder f g) := hm.free_adjoinRoot
  let : Module.Finite ℤ (pairOrder f g) := Module.Finite.trans A _
  let jK : pairOrder f g →+* 𝓞 K :=
    ι.codRestrict (integralClosure ℤ K).toSubring (fun x =>
      (IsIntegral.of_finite ℤ x).map ι.toIntAlgHom)
  refine ⟨K,inferInstance,inferInstance,jK,fun _ _ he => hι (congrArg Subtype.val he),?_⟩
  rw [← finrank_mul_finrank ℤ A (pairOrder f g),← finrank_mul_finrank ℚ F K,hF]
  have h1 : finrank ℤ A = f.natDegree := (AdjoinRoot.powerBasis' hf).finrank
  have h2 : finrank A (pairOrder f g) = h.natDegree := (AdjoinRoot.powerBasis' hm).finrank
  have h3 : finrank F K = (h.map j).natDegree := (AdjoinRoot.powerBasis hi'.ne_zero).finrank
  rw [h1,h2,h3,hm.natDegree_map]

#print axioms exists_full_order
#print axioms irreducible_map_coprime
#print axioms map_injective

end
end Erdos478.RootPairs
