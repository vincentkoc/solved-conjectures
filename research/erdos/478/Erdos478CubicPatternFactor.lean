import Erdos478CubicGapIndependence
import Erdos478GapPatternMeans
import Erdos478GapSplittingDegrees
import Erdos478SexticSplittingDegree

/-!
# A factor of six in factorial collision densities

When every prescribed length is two or at least five, requiring all
three cubic-gap endpoints multiplies the pattern density by one sixth.
The statement allows both saturated and unsaturated lengths.
-/

namespace Erdos478.GapReality
open Polynomial Finset SplittingDensity SexticGap
open scoped Classical
noncomputable section

theorem cubic_saturation_factor (S : Finset ℕ) (hS : ∀ k∈S, realLength k) :
    splitDensity 1 (insert 3 S)=splitDensity 1 S/6 := by
  simp [splitDensity,cubic_gap_degree_factor S hS,Nat.cast_mul,div_eq_mul_inv,mul_comm]

theorem cubic_pattern_factor (S T : Finset ℕ) (hS : ∀ k∈S, realLength k)
    (hT : ∀ k∈T, realLength k) : patternDensity 1 (insert 3 S) T=patternDensity 1 S T/6 := by
  unfold patternDensity
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro U hU
  have hu : ∀ k∈S∪U, realLength k := fun k hk =>
    (mem_union.mp hk).elim (hS k) (fun hj => hT _ (mem_powerset.mp hU hj))
  rw [insert_union,cubic_saturation_factor _ hu]
  ring

theorem two_gap_degree : Module.finrank ℚ (SplitField (gapPoly 2))=2 := by
  let F := (gapPoly 2).map (Int.castRingHom ℚ)
  have hir : Irreducible F := by simpa [F,gapPoly] using GapFamilies.irreducible_gap_rat (by decide : 0<2)
  have hf := gap_degree (by decide : 0<2)
  have hd : F.natDegree=2 := (hf.monic.natDegree_map _).trans hf.natDegree_eq
  have h := Gal.prime_degree_dvd_card hir (hd ▸ Nat.prime_two)
  rw [Gal.card_of_separable hir.separable,hd] at h
  have hup := field_degree_bound (by decide : 0<1) {2} (by simp)
  rw [singleton_gap_degree (by decide : 2≤2)] at hup
  norm_num at hup
  have hp := Module.finrank_pos (R:=ℚ) (M:=SplitField (gapPoly 2))
  change 2∣Module.finrank ℚ (SplitField (gapPoly 2)) at h
  omega

theorem two_three_density : splitDensity 1 {3,2}=1/12 := by
  rw [cubic_saturation_factor {2} (by simp [realLength]),splitDensity,
    singleton_gap_degree (by decide : 2≤2),two_gap_degree]
  norm_num

theorem three_six_density : splitDensity 1 {3,6}=1/144 := by
  rw [cubic_saturation_factor {6} (by simp [realLength]),splitDensity,
    singleton_gap_degree (by decide : 2≤6),sextic_splitting_degree]
  norm_num

#print axioms cubic_saturation_factor
#print axioms cubic_pattern_factor
#print axioms two_gap_degree
#print axioms two_three_density
#print axioms three_six_density
end
end Erdos478.GapReality
