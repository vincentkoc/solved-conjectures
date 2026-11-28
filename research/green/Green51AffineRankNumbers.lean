import Green51AffineRankCounts

/-! # Integer rank distribution of fixed-size subsets of a binary affine space -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold
open scoped Classical

/-- Row `k` counts sets of size `k+1`, with entries indexed by affine dimension. -/
def rankNumbers (n : ℕ) : ℕ → List ℕ
  | 0 => List.ofFn (fun j : Fin (n+1) => if j.val=0 then 2^n else 0)
  | k+1 =>
    let prev := rankNumbers n k
    List.ofFn fun j : Fin (n+1) =>
      (prev.getD j.val 0*(2^j.val-(k+1)) +
        (if j.val=0 then 0 else prev.getD (j.val-1) 0*(2^n-2^(j.val-1))))/(k+2)

private theorem rank_one (n j : ℕ) :
    (rankLayer (𝔽₂ n) 1 j).card = if j=0 then 2^n else 0 := by
  classical
  let K := (univ : Finset (𝔽₂ n)).powersetCard 1
  have zero (D : Finset (𝔽₂ n)) (h : D∈K) : affineRank D=0 := by
    obtain ⟨x,rfl⟩ := card_eq_one.mp (mem_powersetCard.mp h).2
    simp [affineRank,vectorSpan_singleton]
  by_cases h : j=0
  · subst j
    have eq : rankLayer (𝔽₂ n) 1 0=K := filter_true_of_mem zero
    simp [eq,K,𝔽₂,𝔽]
  · rw [if_neg h,card_eq_zero,eq_empty_iff_forall_notMem]
    intro D hD
    obtain ⟨mem,rank⟩ := mem_filter.mp hD
    exact h (rank.symm.trans (zero D mem))

theorem rankNumbers_correct (n k j : ℕ) (bound : j≤n) :
    (rankNumbers n k).getD j 0=(rankLayer (𝔽₂ n) (k+1) j).card := by
  induction k generalizing j with
  | zero =>
    rw [rankNumbers,rank_one,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (by omega)]
    rfl
  | succ k ih =>
    rw [rankNumbers,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (by omega)]
    simp only [Option.getD_some]
    have step := rank_count_step (G := 𝔽₂ n) (k+1) (by omega) j
    have amb : Fintype.card (𝔽₂ n)=2^n := by simp [𝔽₂,𝔽]
    rw [ih j bound,ih (j-1) (by omega),←amb,←step, Nat.mul_div_cancel_left _ (by omega : 0<k+2)]

end Green51AffineTranslation
#print axioms Green51AffineTranslation.rankNumbers_correct
