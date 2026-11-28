import HosoyaIndexTailFactors
import HosoyaPrimePowerIndices

/-! Effective reciprocal tails for Fibonacci return ranks at primes. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

/-- The value at zero makes the weight total on arbitrary finite sets. -/
noncomputable def returnRank (p : ℕ) : ℕ :=
  if h : p=0 then 1 else
    haveI : NeZero p := ⟨h⟩
    fibonacciStepRank p 1

lemma returnRank_spec {p : ℕ} (hp : p.Prime) :
    0 < returnRank p ∧ p ∣ Nat.fib (returnRank p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  simpa [returnRank,hp.ne_zero] using rank_properties p 1

noncomputable def rankWeight (p : ℕ) : ℝ := 1 / ((p:ℝ)*returnRank p)

private lemma sum_weights_le {S : Finset ℕ} {A R : ℕ} (ha : 0 < A) (hr : 0 < R)
    (bounds : ∀ p ∈ S, A≤p ∧ R≤returnRank p) :
    ∑ p ∈ S, rankWeight p ≤ (S.card:ℝ) / (A*R) := by
  calc
    _ ≤ ∑ _p ∈ S, 1 / ((A:ℝ)*R) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨lo,hi⟩ := bounds p hp
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.mul_le_mul lo hi
    _ = _ := by simp [nsmul_eq_mul,div_eq_mul_inv]

private lemma rank_fiber_weight {K r : ℕ} (hk : 64 ≤ K) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ K^2≤p ∧ returnRank p=r) :
    ∑ p ∈ S, rankWeight p ≤ 1 / (12 * (K:ℝ)^2) := by
  rcases S.eq_empty_or_nonempty with empty|⟨p,hp⟩
  · simp [empty]
  have hr : 0 < r := (hS p hp).2.2 ▸ (returnRank_spec (hS p hp).1).1
  have sub : S ⊆ (Nat.fib r).primeFactors := by
    intro q hq
    obtain ⟨prime,lo,eq⟩ := hS q hq
    exact prime.mem_primeFactors (eq ▸ (returnRank_spec prime).2) (Nat.fib_pos.mpr hr).ne'
  have cnt := factor_card_weight (h:=12) (Nat.fib_pos.mpr hr) (fib_le_two_pow r) S sub
    (fun q hq => (show 2^12≤K^2 by nlinarith [Nat.pow_le_pow_left hk 2]).trans (hS q hq).2.1)
  have w := sum_weights_le (A:=K^2) (R:=r) (by positivity) hr
    (fun q hq => ⟨(hS q hq).2.1,(hS q hq).2.2.ge⟩)
  apply w.trans
  push_cast
  have c : 12*(S.card:ℝ)≤r := by exact_mod_cast cnt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left c (sq_nonneg (K:ℝ))]

/-- On [K²,4K²), a short return rank r restricts p to a prime factor of Fᵣ.
Long ranks give a small reciprocal weight without this restriction. -/
theorem rank_shell_bound {K : ℕ} (hk : 64≤K) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ K^2≤p ∧ p<4*K^2) :
    ∑ p ∈ S, rankWeight p ≤ 13/(12*(K:ℝ)) := by
  let A := S.filter fun p => returnRank p < 4*K
  let B := S.filter fun p => ¬ returnRank p < 4*K
  have first : ∑ p ∈ A, rankWeight p ≤ (4*K:ℕ)/(12*(K:ℝ)^2) := by
    have group := sum_fiberwise_of_maps_to (s:=A) (t:=range (4*K)) (g:=returnRank)
      (fun p hp => mem_range.mpr (mem_filter.mp hp).2) rankWeight
    rw [← group]
    calc
      _ ≤ ∑ _r ∈ range (4*K), 1/(12*(K:ℝ)^2) := by
        apply sum_le_sum
        intro r _
        apply rank_fiber_weight hk
        intro p hp
        obtain ⟨ha,eq⟩ := mem_filter.mp hp
        obtain ⟨pr,lo,_⟩ := hS p (mem_filter.mp ha).1
        exact ⟨pr,lo,eq⟩
      _ = _ := by simp [nsmul_eq_mul,div_eq_mul_inv]
  have sub : B⊆Ico (K^2) (4*K^2) := by
    intro p hp
    exact mem_Ico.mpr (hS p (mem_filter.mp hp).1).2
  have size : B.card≤3*K^2 := by
    have := card_le_card sub
    rw [Nat.card_Ico] at this
    omega
  have second := sum_weights_le (S:=B) (A:=K^2) (R:=4*K) (by positivity) (by omega)
    (fun p hp => ⟨(hS p (mem_filter.mp hp).1).2.1, Nat.le_of_not_gt (mem_filter.mp hp).2⟩)
  have c : (B.card:ℝ)≤3*(K:ℝ)^2 := by exact_mod_cast size
  have split : (∑ p ∈ A, rankWeight p)+(∑ p ∈ B, rankWeight p)=∑ p ∈ S, rankWeight p :=
    sum_filter_add_sum_filter_not ..
  rw [← split]
  apply (add_le_add first second).trans
  push_cast
  have pos : (0:ℝ)<K := by exact_mod_cast (by omega : 0 < K)
  calc
    _ ≤ 4*(K:ℝ)/(12*K^2) + (3*K^2 : ℝ)/(K^2*(4*K)) := by gcongr
    _ = _ := by field_simp; ring

private lemma tail_levels (j K : ℕ) (hk : 64≤K) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ K^2≤p ∧ p<(2^j*K)^2) :
    ∑ p ∈ S, rankWeight p ≤ 13/(6*(K:ℝ)) := by
  induction j generalizing K S with
  | zero =>
    have emp : S=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨_,a,b⟩ := hS p hp
      exact (not_lt_of_ge a) (by simpa using b)
    simp [emp]
    positivity
  | succ j ih =>
    let A := S.filter fun p => p < (2*K)^2
    let B := S.filter fun p => ¬p < (2*K)^2
    have a := rank_shell_bound hk A (by
      intro p hp
      obtain ⟨mem,hi⟩ := mem_filter.mp hp
      exact ⟨(hS p mem).1,(hS p mem).2.1,by nlinarith⟩)
    have b := ih (2*K) (by omega) B (by
      intro p hp
      obtain ⟨mem,lo⟩ := mem_filter.mp hp
      obtain ⟨pr,_,hi⟩ := hS p mem
      refine ⟨pr,by omega,?_⟩
      simpa only [pow_succ _ j, mul_assoc] using hi)
    have split : (∑ p ∈ A, rankWeight p)+(∑ p ∈ B, rankWeight p)=∑ p ∈ S, rankWeight p :=
      sum_filter_add_sum_filter_not ..
    rw [←split]
    apply (add_le_add a b).trans
    push_cast
    have pos : (0:ℝ)<K := by exact_mod_cast (by omega : 0 < K)
    apply le_of_eq
    field_simp
    ring

/-- Uniform finite-sum form of the large-rank reciprocal tail. -/
theorem reciprocal_rank_tail {K : ℕ} (hk : 64≤K) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ K^2≤p) :
    ∑ p ∈ S, rankWeight p ≤ 13/(6*(K:ℝ)) := by
  let j := S.sup id
  apply tail_levels j K hk S
  intro p hp
  have le : p ≤ j := Finset.le_sup (f:=id) hp
  have a := j.lt_two_pow_self
  have b : 2^j ≤ 2^j*K := Nat.le_mul_of_pos_right _ (by omega)
  have c : 2^j*K ≤ (2^j*K)^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact ⟨(hS p hp).1,(hS p hp).2,lt_of_le_of_lt le (a.trans_le (b.trans c))⟩

#print axioms reciprocal_rank_tail

#print axioms rank_shell_bound

#print axioms returnRank_spec
#print axioms rank_fiber_weight

end Arxiv.«2211.10788».IndexDivisors
