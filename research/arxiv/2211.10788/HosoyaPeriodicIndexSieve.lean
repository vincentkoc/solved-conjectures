import HosoyaIndexGcdTail
import LucasFibonacciPrimePowerLifts

/-! Periodic finite-prime approximations to index–value coprimality. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

def sample (f : ℕ → Prop) [DecidablePred f] (X : ℕ) := ((Icc 1 X).filter f).card

private lemma sample_le (f : ℕ → Prop) [DecidablePred f] (X : ℕ) : sample f X≤X := by
  simpa [sample] using card_filter_le (Icc 1 X) f

private lemma add_period {f : ℕ → Prop} [DecidablePred f] {D : ℕ} (per : Function.Periodic f D) (a : ℕ) :
    sample f (a+D)=sample f a+D.count f := by
  have interval (n : ℕ) : Icc 1 n=Ico 1 (1+n) := by ext i; simp; omega
  unfold sample
  rw [interval,interval,←Nat.add_assoc,
    ←Ico_union_Ico_eq_Ico (show 1≤1+a by omega) (show 1+a≤1+a+D by omega),filter_union]
  rw [card_union_of_disjoint, Nat.filter_Ico_card_eq_of_periodic (1+a) D f per]
  exact (Ico_disjoint_Ico_consecutive 1 (1+a) (1+a+D)).mono (filter_subset ..) (filter_subset ..)

/-- The count of a periodic predicate differs from its full-period mean times X
by at most one period, including when X is shorter than that period. -/
theorem periodic_sample_error {f : ℕ → Prop} [DecidablePred f] {D : ℕ} (hd : 0 < D)
    (per : Function.Periodic f D) (X : ℕ) :
    |(sample f X:ℝ) - X*((D.count f:ℝ)/D)| ≤ D := by
  let r := X%D
  let q := X/D
  let c := D.count f
  have h (s k : ℕ) : sample f (s+k*D)=sample f s+k*c := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,←Nat.add_assoc,add_period per,ih,Nat.succ_mul]; omega
  have eq : r+q*D=X := by simpa [r,q,Nat.mul_comm] using Nat.mod_add_div X D
  have eqr : (r:ℝ)+q*D=X := by exact_mod_cast eq
  have cnt : sample f X=sample f r+q*c := eq ▸ h r q
  have cp : (c:ℝ)≤D := by exact_mod_cast (Nat.count_le (p:=f) (n:=D))
  have low : (0:ℝ)<D := by exact_mod_cast hd
  have m : (c:ℝ)/D ≤ 1 := (div_le_one low).mpr cp
  have rem : (r:ℝ)≤D := by exact_mod_cast (Nat.mod_lt X hd).le
  have fractional : (r:ℝ)*(c/D)≤D :=
    (mul_le_mul_of_nonneg_left m (by positivity)).trans (by simpa using rem)
  have upper : (sample f r:ℝ)≤D := by
    exact (show (sample f r:ℝ)≤r by exact_mod_cast sample_le f r).trans rem
  change |(sample f X:ℝ)-X*((c:ℝ)/D)|≤D
  rw [cnt,←eqr]
  push_cast
  have id : (q:ℝ)*D*((c:ℝ)/D)=q*c := by field_simp
  rw [add_mul]
  apply abs_le.mpr
  constructor <;> nlinarith [show (0:ℝ)≤r*((c:ℝ)/D) by positivity]

def smallCommon (K n : ℕ) : Prop := ∃ p ∈ range (K^2), p.Prime ∧ p ∣ n ∧ p ∣ lucasFibonacciSum n

instance (K n : ℕ) : Decidable (smallCommon K n) := by unfold smallCommon; infer_instance

def allCommon (n : ℕ) : Prop := ¬n.Coprime (lucasFibonacciSum n)

instance (n : ℕ) : Decidable (allCommon n) := by unfold allCommon; infer_instance

def sievePeriod (K : ℕ) : ℕ := (K^2+1).factorial

theorem small_periodic (K : ℕ) : Function.Periodic (smallCommon K) (sievePeriod K) := by
  intro n
  apply propext
  have step (p : ℕ) (lo : p∈range (K^2)) (hp : p.Prime) :
      (p ∣ n+sievePeriod K ∧ p ∣ lucasFibonacciSum (n+sievePeriod K)) ↔
      (p ∣ n ∧ p ∣ lucasFibonacciSum n) := by
    let : Fact p.Prime := ⟨hp⟩
    have pd : p ∣ sievePeriod K := Nat.dvd_factorial hp.pos (by have := mem_range.mp lo; omega)
    obtain ⟨pos,dvd⟩ := rank_properties p 1
    have bound := rank_le_prime_add_one (p:=p) 1
    have dr : fibonacciStepRank p 1 ∣ sievePeriod K :=
      Nat.dvd_factorial pos (by have := mem_range.mp lo; omega)
    have fib : p ∣ Nat.fib (sievePeriod K) :=
      (by simpa using dvd : p ∣ Nat.fib (fibonacciStepRank p 1)).trans (Nat.fib_dvd _ _ dr)
    rw [Nat.dvd_add_left pd,lucasFibonacciSum_dvd_shift_iff fib]
  constructor
  · rintro ⟨p,lo,pr,hit⟩
    exact ⟨p,lo,pr,(step p lo pr).mp hit⟩
  · rintro ⟨p,lo,pr,hit⟩
    exact ⟨p,lo,pr,(step p lo pr).mpr hit⟩

lemma small_implies_all {K n : ℕ} (h : smallCommon K n) : allCommon n := by
  obtain ⟨p,_,hp,hn,hu⟩ := h
  intro cop
  exact hp.not_dvd_one (cop ▸ Nat.dvd_gcd hn hu)

theorem small_error (K X : ℕ) :
    sample (smallCommon K) X ≤ sample allCommon X ∧
    sample allCommon X ≤ sample (smallCommon K) X + (largeCommon K X).card := by
  constructor
  · apply card_le_card
    intro n hn
    obtain ⟨hx,hs⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hx,small_implies_all hs⟩
  have sub : (Icc 1 X).filter allCommon ⊆ ((Icc 1 X).filter (smallCommon K)) ∪ largeCommon K X := by
    intro n hn
    obtain ⟨hx,bad⟩ := mem_filter.mp hn
    obtain ⟨p,hp,dvd⟩ := Nat.exists_prime_and_dvd (show n.gcd (lucasFibonacciSum n)≠1 from bad)
    obtain ⟨hn,hu⟩ := Nat.dvd_gcd_iff.mp dvd
    by_cases low : p<K^2
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,p,mem_range.mpr low,hp,hn,hu⟩)
    · exact mem_union_right _ (mem_filter.mpr
        ⟨hx,p,hp.mem_primeFactors hn (by have := (mem_Icc.mp hx).1; omega),by omega,hu⟩)
  exact (card_le_card sub).trans (card_union_le ..)

#print axioms periodic_sample_error
#print axioms small_periodic
#print axioms small_error

end Arxiv.«2211.10788».IndexDivisors
