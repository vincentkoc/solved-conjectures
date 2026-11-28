import Erdos478RealPochhammerRoots
import Erdos478RealCubicDegree
import Erdos478GapSplittingTest
import Mathlib.Analysis.Real.Sqrt

/-!
# Independent splitting of the cubic factorial gap

Over any finite collection of gap splitting fields with lengths two
or at least five, adjoining the splitting field of the third gap has
relative degree six. The real-root location is uniform in the lengths.
-/

namespace Erdos478.GapReality
open Polynomial IntermediateField SplittingDensity Finset
open scoped Classical
noncomputable section

/-- The lengths used for real conditioning fields. -/
def realLength (k : ℕ) : Prop := k=2 ∨ 5≤k

private theorem gap_two_real : ((gapPoly 2).map (Int.castRingHom ℝ)).Splits := by
  let u := (1+Real.sqrt 5)/2
  have hu : u*(1-u)= -1 := by
    dsimp [u]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
  have ha : C u+C (1-u)=(1:ℝ[X]) := by rw [← map_add]; simp
  have hb : C u*C (1-u)=(-1:ℝ[X]) := by rw [← map_mul,hu]; simp
  have hf : (gapPoly 2).map (Int.castRingHom ℝ)=X^2-X-1 := by
    simp [gapPoly,descPochhammer]; ring
  rw [hf,show (X^2-X-1 : ℝ[X])=(X-C u)*(X-C (1-u)) by linear_combination X*ha-hb]
  exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)

theorem gap_splits_over_reals {k : ℕ} (hk : realLength k) :
    ((gapPoly k).map (Int.castRingHom ℝ)).Splits := by
  rcases hk with rfl|hk
  · exact gap_two_real
  · simpa [gapPoly] using (splits_real_gap hk).1

private theorem test_splits_over_reals (S : Finset ℕ) (hS : ∀ k∈S, realLength k) :
    ((test 1 S).map (Int.castRingHom ℝ)).Splits := by
  classical
  rw [test,Polynomial.map_prod]
  apply Splits.prod
  intro f hf
  rcases mem_insert.mp hf with rfl|h
  · simp only [cyclotomic_one,Polynomial.map_sub,map_X,Polynomial.map_one]
    simpa using (Splits.X_sub_C (1:ℝ))
  · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
    exact gap_splits_over_reals (hS k hk)

theorem test_insert_gap {k : ℕ} (hk : 2≤k) (S : Finset ℕ)
    (hS : ∀ j∈S, 0<j) (hnew : k∉S) : test 1 (insert k S)=test 1 S*gapPoly k := by
  classical
  have hg := (gap_degree (by omega : 0<k)).natDegree_eq
  have hf : gapPoly k∉factors 1 S := by
    intro h
    rcases mem_insert.mp h with h|h
    · have hh := congrArg natDegree h
      rw [hg,natDegree_cyclotomic] at hh
      simp at hh
      omega
    · obtain ⟨j,hj,he⟩ := mem_image.mp h
      have hh := congrArg natDegree he
      rw [(gap_degree (hS j hj)).natDegree_eq,hg] at hh
      exact hnew (hh ▸ hj)
  have he : factors 1 (insert k S)=insert (gapPoly k) (factors 1 S) := by
    simp [factors,Finset.insert_comm]
  simp only [test,he,prod_insert hf,mul_comm]

private def cubic : Cubic ℚ := ⟨1,-3,2,-1⟩

private theorem cubic_eq_gap : cubic.toPoly=(gapPoly 3).map (Int.castRingHom ℚ) := by
  simp [cubic,Cubic.toPoly,gapPoly,descPochhammer,map_ofNat]
  ring

/-- Exact absolute degree after adding the cubic test. -/
theorem cubic_gap_degree_factor (S : Finset ℕ) (hS : ∀ k∈S, realLength k) :
    Module.finrank ℚ (SplitField (test 1 (insert 3 S))) =
      Module.finrank ℚ (SplitField (test 1 S))*6 := by
  have hpos (j) (hj:j∈S) : 0<j := by rcases hS j hj with rfl|h <;> omega
  have hnew : 3∉S := by
    intro h
    rcases hS 3 h with h|h <;> omega
  have tm := (test_properties (by decide : 0<1) hpos).1
  let P := (test 1 S).map (Int.castRingHom ℚ)
  have hs : (P.map (algebraMap ℚ ℝ)).Splits := by
    rw [show P=(test 1 S).map (Int.castRingHom ℚ) by rfl,Polynomial.map_map,
      show (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ)=Int.castRingHom ℝ from Subsingleton.elim ..]
    exact test_splits_over_reals S hS
  have hi : Irreducible cubic.toPoly := by
    simpa [cubic_eq_gap,gapPoly] using GapFamilies.irreducible_gap_rat (by decide : 0<3)
  have hd : cubic.discr<0 := by norm_num [cubic,Cubic.discr]
  unfold SplitField
  rw [test_insert_gap (by decide : 2≤3) S hpos hnew,Polynomial.map_mul,← cubic_eq_gap]
  exact cubic_compositum_degree P (tm.map _).ne_zero hs cubic rfl hi hd

attribute [-instance] DivisionRing.toRatAlgebra in
/-- A single test with modulus one has exactly the degree of its gap.
The cyclotomic factor at modulus one is the rational linear polynomial X−1. -/
theorem singleton_gap_degree {k : ℕ} (hk : 2≤k) :
    Module.finrank ℚ (SplitField (test 1 {k})) = Module.finrank ℚ (SplitField (gapPoly k)) := by
  let F := (gapPoly k).map (Int.castRingHom ℚ)
  let K := F.SplittingField
  let P := (X-1 : ℚ[X])
  let : IsSplittingField ℚ ℚ P := ⟨by simpa [P] using (Splits.X_sub_C (1:ℚ)),
    eq_top_iff.mpr fun x _ => Subalgebra.algebraMap_mem _ x⟩
  have hF := (gap_degree (by omega : 0<k)).monic.map (Int.castRingHom ℚ)
  let : IsSplittingField ℚ K (F.map (algebraMap ℚ ℚ)) := by
    simpa using (IsSplittingField.splittingField F)
  let : IsSplittingField ℚ K (P*F) := IsSplittingField.mul (K:=ℚ) K P F
    (by simpa [P] using (monic_X_sub_C (1:ℚ)).ne_zero) hF.ne_zero
  have ht : (test 1 {k}).map (Int.castRingHom ℚ)=P*F := by
    have hh := test_insert_gap hk ∅ (by simp) (by simp)
    simpa [test,factors,P,F] using congrArg (Polynomial.map (Int.castRingHom ℚ)) hh
  unfold SplitField
  rw [ht]
  exact (IsSplittingField.algEquiv K (P*F)).toLinearEquiv.finrank_eq.symm

#print axioms gap_splits_over_reals
#print axioms test_insert_gap
#print axioms cubic_gap_degree_factor
#print axioms singleton_gap_degree
end
end Erdos478.GapReality
