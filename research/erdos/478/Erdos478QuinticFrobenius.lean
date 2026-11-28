import Erdos478QuinticFactorCertificate
import Erdos478CommonModularProfile
import Erdos478LowGapBezout

/-! # A modular Frobenius element fixing all smaller roots and transposing two quintic roots -/

namespace Erdos478.QuinticSample
open Polynomial Finset LocalWitness SplittingDensity FrobeniusCounts FirstCollision BinaryGap RootMoments
noncomputable section
set_option maxRecDepth 65536
local instance : Fact (Nat.Prime 9209) := ⟨by norm_num1⟩

private def falling (x : ZMod 9209) : ℕ → ZMod 9209
  | 0 => 1
  | n+1 => falling x n*(x-n)

private theorem eval_gap (x : ZMod 9209) (k : ℕ) :
    (gapPoly k).eval₂ (Int.castRingHom _) x=falling x k-1 := by
  have step (m : ℕ) : (descPochhammer (ZMod 9209) m).eval x=falling x m := by
    induction m with
    | zero => simp [falling]
    | succ m ih => simp [descPochhammer_succ_right,ih,falling]
  rw [gapPoly,← eval_map,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one,eval_sub,eval_one,step]

private theorem count_of_list (k : ℕ) (T : Finset (ZMod 9209))
    (h : ∀ x, (gapPoly k).eval₂ (Int.castRingHom _) x=0 ↔ x∈T) :
    primeRoots (gapPoly k) 9209=T.card := by
  let e : RootPairs.solutions (gapPoly k) (ZMod 9209) ≃ T := Equiv.subtypeEquivRight h
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard T)

theorem root_count2 : primeRoots (gapPoly 2) 9209=2 := by
  let T : Finset (ZMod 9209) := {750,8460}
  rw [count_of_list 2 T]
  · decide +kernel
  · intro x
    rw [eval_gap]
    rw [show falling x 2=x*(x-1) by norm_num [falling]]
    rw [factor2]
    simp [T,mul_eq_zero,sub_eq_zero]

theorem root_count3 : primeRoots (gapPoly 3) 9209=3 := by
  let T : Finset (ZMod 9209) := {4868,6407,7146}
  rw [count_of_list 3 T]
  · decide +kernel
  · intro x
    rw [eval_gap]
    rw [show falling x 3=x*(x-1)*(x-2) by norm_num [falling]]
    rw [factor3]
    simp [T,mul_eq_zero,sub_eq_zero,or_assoc]

theorem root_count4 : primeRoots (gapPoly 4) 9209=4 := by
  let T : Finset (ZMod 9209) := {488,771,8441,8724}
  rw [count_of_list 4 T]
  · decide +kernel
  · intro x
    rw [eval_gap]
    rw [show falling x 4=x*(x-1)*(x-2)*(x-3) by norm_num [falling]]
    rw [factor4]
    simp [T,mul_eq_zero,sub_eq_zero,or_assoc]

theorem root_count5 : primeRoots (gapPoly 5) 9209=3 := by
  let T : Finset (ZMod 9209) := {987,5706,6091}
  rw [count_of_list 5 T]
  · decide +kernel
  · intro x
    rw [eval_gap]
    rw [show falling x 5=x*(x-1)*(x-2)*(x-3)*(x-4) by norm_num [falling]]
    rw [factor5]
    simp [T,mul_eq_zero,sub_eq_zero,quadratic_nonzero,or_assoc]

private theorem sample_profile (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤5 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    ∃ g : Aut K, ∀ k, 2≤k → k≤5 → fixedGap K k g=primeRoots (gapPoly k) 9209 := by
  let S := Icc 2 5
  obtain ⟨g,hg⟩ := RelativeGap.regular_profile K S (fun k h => by have := (mem_Icc.mp h).1; omega)
    (fun k h => split k (mem_Icc.mp h).1 (mem_Icc.mp h).2) 9209 (by
      intro k hk
      obtain ⟨lo,hi⟩ := mem_Icc.mp hk
      apply low_gap_regular lo (by omega)
      interval_cases k <;> decide +kernel)
  exact ⟨g,fun k lo hi => hg k (mem_Icc.mpr ⟨lo,hi⟩)⟩

theorem quintic_profile (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤5 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    ∃ g : Aut K, fixedGap K 2 g=2 ∧ fixedGap K 3 g=3 ∧ fixedGap K 4 g=4 ∧ fixedGap K 5 g=3 := by
  obtain ⟨g,h⟩ := sample_profile K split
  exact ⟨g,(h 2 (by decide) (by decide)).trans root_count2,
    (h 3 (by decide) (by decide)).trans root_count3,
    (h 4 (by decide) (by decide)).trans root_count4,
    (h 5 (by decide) (by decide)).trans root_count5⟩

#print axioms root_count2
#print axioms root_count3
#print axioms root_count4
#print axioms root_count5
#print axioms quintic_profile
end
end Erdos478.QuinticSample
