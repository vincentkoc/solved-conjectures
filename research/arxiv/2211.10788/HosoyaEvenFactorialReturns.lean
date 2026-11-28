import HosoyaIndexCommonDivisors
import Mathlib.Data.Nat.Prime.Factorial

/-! Every even factorial from 4! onward divides the Fibonacci number at its own index. -/

namespace Arxiv.«2211.10788».IndexDivisors

private lemma fib_lift {p r : ℕ} (hp : p.Prime) (hr : p ∣ Nat.fib r) (e : ℕ) :
    p^(e+1) ∣ Nat.fib (r*p^e) := by
  have h := wild_power hp (w^r) (by simpa only [fib_coord] using hr) e
  simpa only [←pow_mul,fib_coord] using h

/-- An even factorial is a Fibonacci return for every one of its divisors. -/
theorem even_factorial_dvd_fib (k : ℕ) :
    (2*(k+2)).factorial ∣ Nat.fib (2*(k+2)).factorial := by
  let M := 2*(k+2)
  change M.factorial ∣ Nat.fib M.factorial
  apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  intro p e hp powD
  cases e with
  | zero => simp
  | succ e =>
    have pD := (dvd_pow_self p (by omega : e+1 ≠ 0)).trans powD
    have le : p ≤ M := hp.dvd_factorial.mp pD
    have ne : p ≠ M := by
      rintro rfl
      have twoD : 2 ∣ M := dvd_mul_right ..
      have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp twoD
      dsimp [M] at eq
      omega
    by_cases h5 : p=5
    · subst p
      have h := fib_lift (r:=5) Nat.prime_five (by decide) e
      exact h.trans (Nat.fib_dvd _ _ (by simpa only [←pow_succ'] using powD))
    let : Fact p.Prime := ⟨hp⟩
    let r := fibonacciStepRank p 1
    obtain ⟨pos,hf⟩ := rank_properties p 1
    have bd := rank_le_prime_add_one (p:=p) 1
    have rD : r ∣ M.factorial := Nat.dvd_factorial pos (by dsimp [r]; omega)
    have cop : r.Coprime (p^e) := ((hp.coprime_iff_not_dvd.mpr (rank_tame h5)).symm).pow_right e
    have prodD := cop.mul_dvd_of_dvd_of_dvd rD ((pow_dvd_pow p (by omega : e ≤ e+1)).trans powD)
    exact (fib_lift hp (r:=r) (by simpa only [one_mul] using hf) e).trans (Nat.fib_dvd _ _ prodD)

#print axioms even_factorial_dvd_fib

end Arxiv.«2211.10788».IndexDivisors
