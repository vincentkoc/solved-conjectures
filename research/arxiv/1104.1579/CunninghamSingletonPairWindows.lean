import CunninghamSelbergSieve
import CunninghamGapClosePairs

/-! Simultaneous exact singleton seeds and their close opposite-kind pairs. -/

namespace CunninghamChain.GapWindow

open Finset Filter Asymptotics
open scoped Topology

noncomputable def singletonSeeds (first : Bool) (N : ℕ) : Finset ℕ := by
  classical exact (range (N+1)).filter (fun n => (if first then IsFirstKindChainOfLength else IsSecondKindChainOfLength) n 1)

noncomputable def bothSeeds (N : ℕ) := singletonSeeds true N ∩ singletonSeeds false N

private lemma card_eq (first : Bool) (N : ℕ) :
    (singletonSeeds first N).card = exactChainCount
      (if first then IsFirstKindChainOfLength else IsSecondKindChainOfLength) 1 N := by
  classical simp [singletonSeeds, exactChainCount]

private lemma seed_mem {first : Bool} {N n : ℕ} (h : n∈singletonSeeds first N) :
    n≤N ∧ n.Prime := by
  classical
  change n∈(range (N+1)).filter _ at h
  obtain ⟨le,h⟩ := mem_filter.mp h
  refine ⟨by simpa using le,?_⟩
  cases first
  · exact h.2.1 0 (by decide)
  · exact h.2.1 0 (by decide)

theorem singleton_proportion (first : Bool) :
    Tendsto (fun N : ℕ => ((singletonSeeds first N).card:ℝ)/N.primeCounting) atTop (𝓝 1) := by
  have nz : ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊:ℝ)≠0 := by
    have p : Tendsto (fun x : ℝ => Nat.primeCounting ⌊x⌋₊) atTop atTop :=
      Nat.tendsto_primeCounting.comp tendsto_nat_floor_atTop
    filter_upwards [(tendsto_atTop.mp p) 1] with x hx
    change 1≤Nat.primeCounting ⌊x⌋₊ at hx
    exact_mod_cast (show Nat.primeCounting ⌊x⌋₊≠0 by omega)
  have h := ((isEquivalent_iff_tendsto_one nz).mp (exactChainCount_one_asymptotic_primeCounting first)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  simpa only [Pi.div_apply,Function.comp_def,Nat.floor_natCast,card_eq] using h

/-- Almost every prime seed has both canonical stops at the first successor. -/
theorem both_proportion :
    Tendsto (fun N : ℕ => ((bothSeeds N).card:ℝ)/N.primeCounting) atTop (𝓝 1) := by
  let ratio (b : Bool) (N : ℕ) := ((singletonSeeds b N).card:ℝ)/N.primeCounting
  have lower : Tendsto (fun N => ratio true N+ratio false N-1) atTop (𝓝 1) := by
    simpa using ((singleton_proportion true).add (singleton_proportion false)).sub_const 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower (singleton_proportion true)
  · filter_upwards [(tendsto_atTop.mp Nat.tendsto_primeCounting) 1] with N hn
    have pos : 0<(N.primeCounting:ℝ) := by exact_mod_cast (show 0<N.primeCounting by omega)
    have bound : (singletonSeeds true N ∪ singletonSeeds false N).card≤N.primeCounting := by
      rw [←Nat.primesLE_card_eq_primeCounting]
      apply card_le_card
      intro n h
      rcases mem_union.mp h with h|h <;> exact Nat.mem_primesLE.mpr (seed_mem h)
    have eq := card_union_add_card_inter (singletonSeeds true N) (singletonSeeds false N)
    change _ + (bothSeeds N).card = _ at eq
    have le : ((singletonSeeds true N).card:ℝ)+(singletonSeeds false N).card ≤
        N.primeCounting+(bothSeeds N).card := by exact_mod_cast (show _ by omega : (singletonSeeds true N).card+
          (singletonSeeds false N).card≤N.primeCounting+(bothSeeds N).card)
    dsimp only [ratio]
    field_simp
    linarith
  · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (by exact_mod_cast card_le_card (inter_subset_left (s₂:=singletonSeeds false n) (s₁:=singletonSeeds true n))) (by positivity)

#print axioms singleton_proportion
#print axioms both_proportion

/-- The bound counts pairs of canonical exact chains, with the first kind at
the smaller seed and the second kind at the larger seed. -/
noncomputable def exactPairWeight (N H : ℕ) :=
  pairWeight H (singletonSeeds true N) (singletonSeeds false N)

theorem exact_pair_finite (N H : ℕ) :
    (H*(bothSeeds N).card)^2 ≤ (N+H)*(H*(bothSeeds N).card+2*exactPairWeight N H) := by
  have left : bothSeeds N ⊆ singletonSeeds true N := inter_subset_left
  have right : bothSeeds N ⊆ singletonSeeds false N := inter_subset_right
  have bigger : pairWeight H (bothSeeds N) (bothSeeds N) ≤ exactPairWeight N H := by
    unfold pairWeight exactPairWeight
    exact (sum_le_sum (fun _ _ => sum_le_sum_of_subset_of_nonneg right (fun _ _ _ => Nat.zero_le _))).trans
      (sum_le_sum_of_subset_of_nonneg left (fun _ _ _ => Nat.zero_le _))
  exact (close_pairs (bothSeeds N) (fun n h => (seed_mem (left h)).1) H).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ bigger) _))

#print axioms exact_pair_finite

end CunninghamChain.GapWindow
