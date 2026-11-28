import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes

/-! The two possible residues of an upper term at a prime index. -/

namespace Arxiv.«2211.10788»

private lemma golden_power {K : Type*} [CommRing K] {a : K} (ha : a^2=a+1) (n : ℕ) :
    a^n = (Nat.fib n : K)*(a-4)+(lucasFibonacciSum n : K) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucas_fibonacci_sum_zero]
  | one => simp [lucas_fibonacci_sum_one]
  | more n h₀ h₁ =>
    rw [pow_add,ha,mul_add,mul_one,←pow_succ,h₁,h₀,Nat.fib_add_two,lucas_fibonacci_sum_recurrence]
    push_cast
    ring

/-- At a prime index greater than five, Frobenius either fixes the two
Fibonacci roots or interchanges them. The upper entry is 4 or −3 modulo p. -/
theorem upper_at_prime_frobenius {p : ℕ} (hp : p.Prime) (hbig : 5<p) :
    (lucasFibonacciSum p : ZMod p)=4 ∨ (lucasFibonacciSum p : ZMod p)= -3 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  open Polynomial in
    obtain ⟨a,ha⟩ := IsAlgClosed.exists_root (X^2-X-1 : K[X])
      (by have hd : (X^2-X-1 : K[X]).degree=2 := by compute_degree!
          rw [hd]; decide)
  have hA : a^2=a+1 := by
    simp only [Polynomial.IsRoot,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one] at ha
    linear_combination ha
  let b := 1-a
  have hB : b^2=b+1 := by dsimp [b]; linear_combination hA
  have hsep : a-b≠0 := by
    intro h
    have h5 : (a-b)^2=5 := by dsimp [b]; linear_combination 4*hA
    rw [h,zero_pow (by decide)] at h5
    exact (Nat.not_dvd_of_pos_of_lt (by decide) hbig) ((CharP.cast_eq_zero_iff K p 5).mp h5.symm)
  let F := frobenius K p
  have hpoly : (F a-a)*(F a-b)=0 := by
    have h := congrArg F hA
    simp only [map_pow,map_add,map_one] at h
    dsimp [b]
    linear_combination h-hA
  have hbF : F b=1-F a := by simp [b]
  have h₁ := golden_power hA p
  have h₂ := golden_power hB p
  change F a=_ at h₁
  change F b=_ at h₂
  have inj := (algebraMap (ZMod p) K).injective
  rcases mul_eq_zero.mp hpoly with h|h
  · rw [sub_eq_zero.mp h] at h₁ hbF
    rw [hbF] at h₂
    have h' : (a-b)*((Nat.fib p:K)-1)=0 := by dsimp [b] at *; linear_combination h₂-h₁
    have hF := sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hsep)
    rw [hF] at h₁
    left; apply inj; simp only [map_natCast, map_ofNat]; linear_combination -h₁
  · rw [sub_eq_zero.mp h] at h₁ hbF
    rw [hbF] at h₂
    have h' : (a-b)*((Nat.fib p:K)+1)=0 := by dsimp [b] at *; linear_combination h₂-h₁
    have hF : (Nat.fib p:K)= -1 := by linear_combination ((mul_eq_zero.mp h').resolve_left hsep)
    rw [hF] at h₁
    right; apply inj; simp only [map_neg, map_ofNat, map_natCast]; dsimp [b] at h₁; linear_combination -h₁

#print axioms upper_at_prime_frobenius

end Arxiv.«2211.10788»
