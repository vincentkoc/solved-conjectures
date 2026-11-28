import Erdos478ExactEndpointCounts
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The factorial gap of length three

The cubic gap has splitting degree six. A square root of its discriminant
gives the quadratic subfield and one of its roots gives a cubic subfield.
The degree and the first root moment determine every local frequency.
-/

namespace Erdos478.CollisionLaw
noncomputable section
open Polynomial Finset Filter Topology IntermediateField SplittingDensity RootMoments
open scoped Classical

private def cubic : Cubic ℚ := ⟨1,-3,2,-1⟩

private theorem cubic_poly : cubic.toPoly=(gapPoly 3).map (Int.castRingHom ℚ) := by
  simp [cubic,Cubic.toPoly,gapPoly,show (3:ℕ)=2+1 by rfl,descPochhammer_succ_right]
  norm_num [map_ofNat]
  ring

private theorem sqrt_disc (K : Type) [Field K] [Algebra ℚ K]
    (hs : (cubic.toPoly.map (algebraMap ℚ K)).Splits) : ∃ t : K, t^2= -23 := by
  have h : cubic.a≠0 := by decide
  obtain ⟨x,y,z,hxyz⟩ := (Cubic.splits_iff_roots_eq_three h).mp hs
  have H := Cubic.discr_eq_prod_three_roots h hxyz
  have he : cubic.discr= -23 := by norm_num [cubic,Cubic.discr]
  rw [he] at H
  exact ⟨_,by simpa using H.symm⟩

private theorem even_degree {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {t : K} (ht : t^2= -23) : 2 ∣ Module.finrank ℚ K := by
  let q : ℚ[X] := X^2 - C (-23)
  have hm : q.Monic := monic_X_pow_sub_C _ (by decide)
  have hd : q.natDegree=2 := natDegree_X_pow_sub_C
  have hir : Irreducible q := by
    apply (hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro x hx
    have h := (mem_roots hm.ne_zero).mp hx
    simp [q,IsRoot] at h
    nlinarith [sq_nonneg x]
  have hzero : aeval t q=0 := by simp [q,ht]
  have hmin := minpoly.eq_of_irreducible_of_monic hir hzero hm
  use Module.finrank ℚ⟮t⟯ K
  rw [← Module.finrank_mul_finrank ℚ ℚ⟮t⟯ K,IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ t)]
  rw [← hmin,hd]

/-- The discriminant is minus twenty-three and the cubic is irreducible. -/
theorem cubic_splitting_degree : Module.finrank ℚ (SplitField (gapPoly 3))=6 := by
  let F := (gapPoly 3).map (Int.castRingHom ℚ)
  let K := F.SplittingField
  have hir : Irreducible F := by simpa [F,gapPoly] using GapFamilies.irreducible_gap_rat (by decide : 0<3)
  have hg := gap_degree (by decide : 0<3)
  have hd : F.natDegree=3 := (hg.monic.natDegree_map _).trans hg.natDegree_eq
  have h3 := Gal.prime_degree_dvd_card hir (hd ▸ Nat.prime_three)
  rw [Gal.card_of_separable hir.separable,hd] at h3
  obtain ⟨t,ht⟩ := sqrt_disc K (cubic_poly ▸ SplittingField.splits F)
  have h2 := even_degree ht
  let : Fact ((F.map (algebraMap ℚ K)).Splits) := ⟨SplittingField.splits F⟩
  have H := Nat.card_le_card_of_injective _ (Gal.galActionHom_injective F K)
  rw [Nat.card_perm,Nat.card_coe_set_eq,Gal.card_of_separable hir.separable] at H
  have h6 : Module.finrank ℚ K≤6 := H.trans (Nat.factorial_le ((F.ncard_rootSet_le K).trans_eq hd))
  change Module.finrank ℚ K=6
  have hpos := Module.finrank_pos (R:=ℚ) (M:=K)
  change 3 ∣ Module.finrank ℚ K at h3
  omega

private theorem cubic_counts {K : Type*} [Field K] {F : K[X]} (h : F.natDegree=3) :
    F.roots.card=0 ∨ F.roots.card=1 ∨ F.roots.card=3 := by
  have hle := (card_roots' F).trans_eq h
  have hne : F.roots.card≠2 := by
    intro hc
    obtain ⟨q,_,hd,hq⟩ := exists_prod_multiset_X_sub_C_mul F
    have hd' : q.natDegree=1 := by omega
    have hcard := splits_iff_card_roots.mp (Splits.of_natDegree_eq_one hd')
    rw [hq,hd',Multiset.card_zero] at hcard
    contradiction
  omega

private def coefficients (j : ℕ) : ℤ × ℤ × ℤ :=
  if j=0 then (1,-1,2) else if j=1 then (0,1,-3) else if j=3 then (0,0,1) else (0,0,0)

def cubicFrequency (j : ℕ) : ℚ :=
  if j=0 then 1/3 else if j=1 then 1/2 else if j=3 then 1/6 else 0

private theorem cubic_indicator (j p : ℕ) [Fact p.Prime] (hp : cutoff 3<p) :
    event (fun p => (endpoints 3 p).card=j) p =
      (coefficients j).1 + (coefficients j).2.1 * RootMoments.roots (gapPoly 3) p +
        (coefficients j).2.2 * indicator (gapPoly 3) p := by
  classical
  let f := gapPoly 3
  let F := f.map (Int.castRingHom (ZMod p))
  have hg := gap_degree (by decide : 0<3)
  have hd : F.natDegree=3 := (hg.monic.natDegree_map _).trans hg.natDegree_eq
  have hs := GapFamilies.separable_mod_above_resultant f (hg.natDegree_eq ▸ (by decide : 3≠0))
    (by simpa [f,gapPoly] using (GapFamilies.irreducible_gap_rat (by decide : 0<3)).separable)
    ((le_max_right ..).trans_lt hp)
  have hr := count_roots f hg.monic p hs
  have he := endpoint_count (by decide : 2≤3) hp
  change (endpoints 3 p).card=F.roots.card at he
  have hsplit : F.Splits ↔ F.roots.card=3 := splits_iff_card_roots.trans (by rw [hd])
  have hr' : RootMoments.roots (gapPoly 3) p=(F.roots.card:ℝ) := hr
  have hs' : ((gapPoly 3).map (Int.castRingHom (ZMod p))).Splits ↔ F.roots.card=3 := hsplit
  simp only [event,indicator,he,hr',hs']
  rcases cubic_counts hd with h|h|h <;> rw [h] <;>
    by_cases a : j=0 <;> by_cases b : j=1 <;> by_cases c : j=3 <;>
    norm_num [coefficients,a,b,c,eq_comm]

/-- At gap three the proportions for zero, one and three positive pairs
are respectively one third, one half and one sixth. -/
theorem cubic_count_mean (A : PrimeAverage) (j : ℕ) :
    Tendsto (fun X => A.avg X (event (fun p => (endpoints 3 p).card=j))) atTop
      (𝓝 (cubicFrequency j : ℝ)) := by
  let f := gapPoly 3
  have hg := gap_degree (by decide : 0<3)
  have hir : Irreducible (f.map (Int.castRingHom ℚ)) := by simpa [f,gapPoly] using GapFamilies.irreducible_gap_rat (by decide : 0<3)
  have H := split_mean A f hg.monic (hg.natDegree_eq ▸ (by decide : 0<3)) hir.separable
  rw [show Module.finrank ℚ (SplitField f)=6 from cubic_splitting_degree] at H
  let a : ℝ := (coefficients j).1
  let b : ℝ := (coefficients j).2.1
  let c : ℝ := (coefficients j).2.2
  have eq : a*1+b*1+c*((6:ℕ):ℝ)⁻¹ = (cubicFrequency j:ℝ) := by
    by_cases h : j=0 <;> by_cases h' : j=1 <;> by_cases h'' : j=3 <;>
      norm_num [a,b,c,coefficients,cubicFrequency,h,h',h'']
  apply mean_of_change A (b:=a • (1:ℕ→ℝ) + b • RootMoments.roots f + c • indicator f) (cutoff 3)
  · intro p hp hpr
    let : Fact p.Prime := ⟨hpr⟩
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.one_apply,mul_one] using cubic_indicator j p hp
  · rw [← eq]
    simpa only [map_add,map_smul,smul_eq_mul] using
      (((constant_mean A).const_mul a).add ((first_mean A f hg.monic hir).const_mul b)).add (H.const_mul c)

#print axioms cubic_count_mean

#print axioms cubic_splitting_degree
end
end Erdos478.CollisionLaw
