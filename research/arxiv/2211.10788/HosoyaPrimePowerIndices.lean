import LucasFibonacciProgressionDivisors

/-! Frobenius on the two Fibonacci roots controls rank and value at prime-power indices. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Polynomial

private lemma fibonacci_roots (p : ℕ) [Fact p.Prime] (h5 : p≠5) :
    let K := AlgebraicClosure (ZMod p)
    ∃ a b : K, a^2=a+1 ∧ b^2=b+1 ∧ a+b=1 ∧ a≠b := by
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_root (X^2-X-1 : K[X])
    (by have h : (X^2-X-1 : K[X]).degree=2 := by compute_degree!
        rw [h]; decide)
  simp only [IsRoot.def,eval_sub,eval_pow,eval_X,eval_one] at ha
  refine ⟨a,1-a,by linear_combination ha,by linear_combination ha,by ring,?_⟩
  intro he
  have hz : (5:K)=0 := by linear_combination (2*a-1)*he - 4*ha
  exact h5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp ((CharP.cast_eq_zero_iff K p 5).mp hz))

private lemma binet {K : Type*} [Field K] {a b : K} (ha : a^2=a+1) (hb : b^2=b+1)
    (hs : a+b=1) (n : ℕ) :
    (a-b)*(Nat.fib n : K)=a^n-b^n ∧
      (a-b)*(lucasFibonacciSum n : K)=(3+a)*a^n-(3+b)*b^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucasFibonacciSum]
  | one =>
    norm_num [lucasFibonacciSum]
    linear_combination (b-a)*hs
  | more n h₀ h₁ =>
    rw [Nat.fib_add_two,lucas_fibonacci_sum_recurrence]
    push_cast
    rw [mul_add,mul_add,h₀.1,h₁.1,h₀.2,h₁.2,pow_add a n 2,pow_add b n 2,ha,hb,pow_succ a n,pow_succ b n]
    constructor <;> ring

/-- Multiplication of the Fibonacci index by a power of p leaves divisibility
by p unchanged at every prime other than the ramified prime five. -/
theorem fib_frobenius_dvd {p : ℕ} [Fact p.Prime] (h5 : p≠5) (e t : ℕ) :
    p ∣ Nat.fib (p^e*t) ↔ p ∣ Nat.fib t := by
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨a,b,ha,hb,hs,hab⟩ := fibonacci_roots p h5
  have hf (j : ℕ) : p ∣ Nat.fib j ↔ a^j=b^j := by
    rw [←CharP.cast_eq_zero_iff K, ←mul_eq_zero_iff_left (sub_ne_zero.mpr hab),
      (binet ha hb hs j).1,sub_eq_zero]
  rw [hf,hf,Nat.mul_comm,pow_mul,pow_mul]
  exact (iterateFrobenius K p e).injective.eq_iff

/-- At a prime-power index, the upper value reduces to 4 or −3 modulo its
prime base. The ramified prime is handled separately by its five-step period. -/
theorem upper_prime_power_residues {p : ℕ} [Fact p.Prime] (h5 : p≠5) (e : ℕ) :
    (lucasFibonacciSum (p^e) : ZMod p)=4 ∨ (lucasFibonacciSum (p^e) : ZMod p)= -3 := by
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨a,b,ha,hb,hs,hab⟩ := fibonacci_roots p h5
  let F := iterateFrobenius K p e
  have hma : (F a)^2=F a+1 := by simpa using congrArg F ha
  have hms : F a+F b=1 := by simpa using congrArg F hs
  have prod : (F a-a)*(F a-b)=0 := by
    linear_combination hma-ha+(a-F a)*hs
  have eq := (binet ha hb hs (p^e)).2
  change (a-b)*(lucasFibonacciSum (p^e) : K)=(3+a)*F a-(3+b)*F b at eq
  have inj := (algebraMap (ZMod p) K).injective
  rcases mul_eq_zero.mp prod with h|h
  · have e₁ := sub_eq_zero.mp h
    have e₂ : F b=b := by linear_combination hms-hs-e₁
    rw [e₁,e₂] at eq
    left
    apply inj
    simp only [map_natCast,map_ofNat]
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab)
    linear_combination eq+(a-b)*hs
  · have e₁ := sub_eq_zero.mp h
    have e₂ : F b=a := by linear_combination hms-hs-e₁
    rw [e₁,e₂] at eq
    right
    apply inj
    simp only [map_natCast,map_ofNat,map_neg]
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab)
    linear_combination eq

lemma rank_properties (p d : ℕ) [NeZero p] : 0<fibonacciStepRank p d ∧
    p ∣ Nat.fib (d*fibonacciStepRank p d) := by
  unfold fibonacciStepRank
  exact Nat.find_spec (p:=fun t => 0<t ∧ p ∣ Nat.fib (d*t)) _

lemma rank_min (p d t : ℕ) [NeZero p] (ht : 0<t) (hf : p ∣ Nat.fib (d*t)) :
    fibonacciStepRank p d ≤ t := by
  unfold fibonacciStepRank
  exact Nat.find_min' _ ⟨ht,hf⟩

/-- The Fibonacci return rank on any step is at most p+1. For p≠5 the
two roots are fixed or exchanged by Frobenius, giving a return at p−1 or p+1. -/
theorem rank_le_prime_add_one {p : ℕ} [Fact p.Prime] (d : ℕ) :
    fibonacciStepRank p d ≤ p+1 := by
  have hp : p.Prime := Fact.out
  have lift (s : ℕ) (hs : 0<s) (hf : p ∣ Nat.fib s) (le : s≤p+1) :
      fibonacciStepRank p d ≤ p+1 :=
    (rank_min p d s hs (hf.trans (Nat.fib_dvd _ _ (dvd_mul_left s d)))).trans le
  by_cases h5 : p=5
  · subst p
    exact lift 5 (by decide) (by decide) (by decide)
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨a,b,ha,hb,hs,hab⟩ := fibonacci_roots p h5
  let F := frobenius K p
  have hma : (F a)^2=F a+1 := by simpa using congrArg F ha
  have hms : F a+F b=1 := by simpa using congrArg F hs
  have prod : (F a-a)*(F a-b)=0 := by linear_combination hma-ha+(a-F a)*hs
  have a0 : a≠0 := by rintro rfl; simp at ha
  have b0 : b≠0 := by rintro rfl; simp at hb
  have hit (t : ℕ) (eq : a^t=b^t) : p ∣ Nat.fib t := by
    apply (CharP.cast_eq_zero_iff K p _).mp
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab)
    rw [mul_zero,(binet ha hb hs t).1,eq,sub_self]
  rcases mul_eq_zero.mp prod with h|h
  · have e₁ := sub_eq_zero.mp h
    have e₂ : F b=b := by linear_combination hms-hs-e₁
    have fix {x : K} (hx : x≠0) (he : F x=x) : x^(p-1)=1 := by
      apply mul_right_cancel₀ hx
      rw [←pow_succ,Nat.sub_add_cancel hp.one_le,one_mul]
      exact he
    exact lift (p-1) (by have := hp.one_lt; omega)
      (hit _ ((fix a0 e₁).trans (fix b0 e₂).symm)) (by omega)
  · have e₁ := sub_eq_zero.mp h
    have e₂ : F b=a := by linear_combination hms-hs-e₁
    apply lift (p+1) (by omega) _ le_rfl
    apply hit
    simp only [pow_succ]
    change F a*a=F b*b
    rw [e₁,e₂,mul_comm]

#print axioms rank_le_prime_add_one

theorem rank_tame {p : ℕ} [Fact p.Prime] (h5 : p≠5) :
    ¬p ∣ fibonacciStepRank p 1 := by
  obtain ⟨hr,hf⟩ := rank_properties p 1
  simp only [one_mul] at hf
  rintro ⟨m,hm⟩
  rw [hm] at hf hr
  have ht := (fib_frobenius_dvd h5 1 m).mp (by simpa using hf)
  have hmpos : 0 < m := Nat.pos_of_mul_pos_left hr
  have le := rank_min p 1 m hmpos (by simpa using ht)
  rw [hm] at le
  have := Nat.mul_lt_mul_of_pos_right (Fact.out : p.Prime).one_lt hmpos
  omega

lemma rank_prime_power_step {p : ℕ} [Fact p.Prime] (h5 : p≠5) (e : ℕ) :
    fibonacciStepRank p (p^e)=fibonacciStepRank p 1 := by
  obtain ⟨h₁,h₂⟩ := rank_properties p (p^e)
  obtain ⟨h₃,h₄⟩ := rank_properties p 1
  exact le_antisymm (rank_min _ _ _ h₃ ((fib_frobenius_dvd h5 _ _).mpr (by simpa using h₄)))
    (rank_min _ _ _ h₁ (by simpa using (fib_frobenius_dvd h5 _ _).mp h₂))

#print axioms fib_frobenius_dvd
#print axioms upper_prime_power_residues
#print axioms rank_tame

end Arxiv.«2211.10788».IndexDivisors
