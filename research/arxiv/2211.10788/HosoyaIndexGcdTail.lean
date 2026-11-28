import HosoyaReciprocalRankTail

/-! Counting large prime obstructions to coprimality of a Hosoya index and its value. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

def commonHits (p X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n => p ∣ n ∧ p ∣ lucasFibonacciSum n

private lemma hits_modEq {p X a b : ℕ} (hp : p.Prime) (h5 : p ≠ 5)
    (ha : a ∈ commonHits p X) (hb : b ∈ commonHits p X) :
    a ≡ b [MOD p*returnRank p] := by
  let : Fact p.Prime := ⟨hp⟩
  wlog le : a ≤ b generalizing a b
  · exact (this hb ha (by omega)).symm
  obtain ⟨_,⟨s,rfl⟩,as⟩ := mem_filter.mp ha
  obtain ⟨_,⟨t,rfl⟩,bs⟩ := mem_filter.mp hb
  have st : s≤t := Nat.le_of_mul_le_mul_left le hp.pos
  have gap := (lucasFibonacciSum_dvd_after_hit_iff as p (t-s)).mp
    (by simpa only [←Nat.mul_add,Nat.add_sub_of_le st] using bs)
  have eq : fibonacciStepRank p p = returnRank p := by
    simpa [returnRank,hp.ne_zero] using rank_prime_power_step (p:=p) h5 1
  rw [eq] at gap
  exact ((Nat.modEq_iff_dvd' st).mpr gap).mul_left' p

/-- At any prime away from five, simultaneous hits occupy at most one residue
class of the index modulo p times its Fibonacci return rank. -/
theorem common_hits_le {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) (X : ℕ) :
    ((commonHits p X).card:ℝ) ≤ X*rankWeight p+1 := by
  let M := p*returnRank p
  have hc := card_le_card_of_injOn (s:=commonHits p X) (t:=range (X/M+1))
    (fun n : ℕ => n/M)
    (fun n hn => mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hn).1).2)))
    (by
      intro a ha b hb q
      have rem : a%M=b%M := hits_modEq hp h5 ha hb
      have e₁ := Nat.mod_add_div a M
      have e₂ := Nat.mod_add_div b M
      change a/M=b/M at q
      rw [rem,q] at e₁
      exact e₁.symm.trans e₂)
  rw [card_range] at hc
  have cast : ((commonHits p X).card:ℝ) ≤ ((X/M:ℕ):ℝ)+1 := by exact_mod_cast hc
  apply cast.trans
  apply add_le_add_left
  simpa [rankWeight, M, div_eq_mul_inv] using (Nat.cast_div_le (α:=ℝ) (m:=X) (n:=M))

/-- Positive indices at most X with a common prime divisor at least K². -/
def largeCommon (K X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n => ∃ p ∈ n.primeFactors, K^2≤p ∧ p ∣ lucasFibonacciSum n

/-- A finite error bound with a free cut PT≥X. Taking X=L³, P=L², T=L
gives a power-saving error of order X^(2/3). -/
theorem large_common_tail {K : ℕ} (hk : 64≤K) (X P T : ℕ) (cut : X≤P*T) :
    ((largeCommon K X).card:ℝ) ≤ 13*X/(6*(K:ℝ)) + P + 8*(T:ℝ)^2 := by
  let S := (Icc 1 P).filter fun p => p.Prime ∧ K^2≤p
  let big := (Icc 1 X).filter fun n => ∃ p ∈ n.primeFactors,
      max P 5 < p ∧ p ∣ lucasFibonacciSum n
  have sub : largeCommon K X ⊆ S.biUnion (fun p => commonHits p X) ∪ big := by
    intro n hn
    obtain ⟨hx,p,hp,low,hit⟩ := mem_filter.mp hn
    obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    by_cases small : p≤P
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨pr.pos,small⟩,pr,low⟩,mem_filter.mpr ⟨hx,dvd,hit⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,p,hp,max_lt (by omega) (by nlinarith),hit⟩)
  have c : (largeCommon K X).card ≤ (∑ p ∈ S, (commonHits p X).card)+8*T^2 :=
    (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add card_biUnion_le
      (very_large_prime_count X P T cut)))
  have step : (∑ p ∈ S, ((commonHits p X).card:ℝ)) ≤ ∑ p ∈ S, (X*rankWeight p+1) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨_,pr,lo⟩ := mem_filter.mp hp
    exact common_hits_le pr (by nlinarith) X
  have hsmall : S.card≤P := by
    simpa using card_le_card (filter_subset (fun p => p.Prime ∧ K^2≤p) (Icc 1 P))
  have hweight := reciprocal_rank_tail hk S (fun p hp => (mem_filter.mp hp).2)
  rw [sum_add_distrib,←mul_sum] at step
  simp only [sum_const,nsmul_eq_mul,mul_one] at step
  have c' : ((largeCommon K X).card:ℝ) ≤ (∑ p ∈ S, ((commonHits p X).card:ℝ))+8*(T:ℝ)^2 := by
    exact_mod_cast c
  have hcount : (S.card:ℝ)≤P := by exact_mod_cast hsmall
  have hmul := mul_le_mul_of_nonneg_left hweight (show (0:ℝ)≤X by positivity)
  calc
    _ ≤ _ := c'
    _ ≤ ((X:ℝ)*(13/(6*K))+P)+8*T^2 := by linarith
    _ = _ := by ring

#print axioms common_hits_le
#print axioms large_common_tail

end Arxiv.«2211.10788».IndexDivisors
