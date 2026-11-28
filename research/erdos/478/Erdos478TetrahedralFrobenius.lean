import Erdos478TetrahedralSmallPrime
import Erdos478TetrahedralQuartic
import Erdos478CommonModularProfile
import Erdos478LowGapBezout

/-! # A single Frobenius element for the lower four gaps and the quartic vertices -/

namespace Erdos478.TetrahedralSample
open Polynomial Finset LocalWitness SplittingDensity FrobeniusCounts FirstCollision BinaryGap RootMoments
open TetrahedralGap
noncomputable section
local instance : Fact (Nat.Prime 1439) := ⟨by norm_num1⟩

private def falling (x : ZMod 1439) : ℕ → ZMod 1439
  | 0 => 1
  | n+1 => falling x n*(x-n)

private theorem eval_gap (x : ZMod 1439) (k : ℕ) :
    (gapPoly k).eval₂ (Int.castRingHom _) x=falling x k-1 := by
  have step (m : ℕ) : (descPochhammer (ZMod 1439) m).eval x=falling x m := by
    induction m with
    | zero => simp [falling]
    | succ m ih => simp [descPochhammer_succ_right,ih,falling]
  rw [gapPoly,← eval_map,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one,eval_sub,eval_one,step]

private theorem count_of_list (f : ℤ[X]) (T : Finset (ZMod 1439))
    (h : ∀ x, f.eval₂ (Int.castRingHom _) x=0 ↔ x∈T) : primeRoots f 1439=T.card := by
  let e : RootPairs.solutions f (ZMod 1439) ≃ T := Equiv.subtypeEquivRight h
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard T)

theorem root_counts : primeRoots (gapPoly 2) 1439=2 ∧ primeRoots (gapPoly 3) 1439=0 ∧
    primeRoots (gapPoly 4) 1439=4 ∧ primeRoots (gapPoly 5) 1439=2 ∧ primeRoots (quartic ℤ) 1439=2 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [count_of_list _ {701,739}]
    · decide +kernel
    · intro x
      rw [eval_gap,show falling x 2=x*(x-1) by norm_num [falling],gap_two]
      simp [sub_eq_zero]
  · rw [count_of_list _ ∅]
    · rfl
    · intro x
      rw [eval_gap,show falling x 3=x*(x-1)*(x-2) by norm_num [falling]]
      simp [cubic_nonzero]
  · rw [count_of_list _ {50,333,1109,1392}]
    · decide +kernel
    · intro x
      rw [eval_gap,show falling x 4=x*(x-1)*(x-2)*(x-3) by norm_num [falling],gap_four]
      simp [sub_eq_zero,or_assoc]
  · rw [count_of_list _ {68,743}]
    · decide +kernel
    · intro x
      rw [eval_gap,show falling x 5=x*(x-1)*(x-2)*(x-3)*(x-4) by norm_num [falling],gap_five]
      simp [sub_eq_zero,quintic_factor_nonzero]
  · rw [count_of_list _ {1131,1331}]
    · decide +kernel
    · intro x
      rw [← eval_map,quartic_map]
      simp only [quartic,eval_add,eval_sub,eval_pow,eval_X,eval_mul,eval_C,quartic_split]
      simp [sub_eq_zero,quadratic_nonzero]

theorem simultaneous_profile (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤5 → ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (qsplit : ((quartic ℚ).map (algebraMap ℚ K)).Splits) :
    ∃ g : Aut K, fixedGap K 2 g=2 ∧ fixedGap K 3 g=0 ∧ fixedGap K 4 g=4 ∧
      fixedGap K 5 g=2 ∧ fixed K (quartic ℤ) g=2 := by
  obtain ⟨g,hg⟩ := simultaneous_witness K 1439
  have h (k : ℕ) (lo : 2≤k) (hi : k≤5) : fixedGap K k g=primeRoots (gapPoly k) 1439 := by
    let f := gapPoly k
    have rat : f.map (Int.castRingHom ℚ)=rationalGap k := by simp [f,gapPoly,rationalGap]
    have sp := split k lo hi
    rw [← rat,map_integer_poly] at sp
    have sep := (GapFamilies.irreducible_gap_rat (by omega : 0<k)).separable
    change (rationalGap k).Separable at sep
    rw [← rat] at sep
    have mapped := sep.map (f:=algebraMap ℚ K)
    rw [map_integer_poly] at mapped
    have reg := low_gap_regular (p:=1439) lo (by omega : k≤10) (by interval_cases k <;> decide +kernel)
    have eq := hg f (gap_degree (by omega : 0<k)).monic mapped sp reg
    unfold fixed rootType at eq
    rwa [rat] at eq
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have reg := quartic_separable (ZMod 1439) (by decide +kernel)
  have eq := hg (quartic ℤ) (quartic_monic _) (by rw [quartic_map]; exact quartic_separable _ (by norm_num))
    (by simpa only [quartic_map] using qsplit) (by rwa [quartic_map])
  obtain ⟨a,b,c,d,e⟩ := root_counts
  exact ⟨g,(h 2 (by decide) (by decide)).trans a,(h 3 (by decide) (by decide)).trans b,
    (h 4 (by decide) (by decide)).trans c,(h 5 (by decide) (by decide)).trans d,eq.trans e⟩

#print axioms root_counts
#print axioms simultaneous_profile
end
end Erdos478.TetrahedralSample
