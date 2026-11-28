import HosoyaSmallExponentSieve
import HosoyaProperPowerIndices

/-! Prime exponents in a proper power of the neighboring Fibonacci–Lucas product. -/

namespace Arxiv.«2211.10788»

/-- Every prime divisor of the exponent of a neighboring product is at least 101. -/
theorem neighboring_power_prime_divisor {m y k p : ℕ}
    (he : lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m = y^k)
    (hp : p.Prime) (hd : p ∣ k) : 101 ≤ p := by
  obtain ⟨s,rfl⟩ := hd
  have hpow : lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m = (y^s)^p := by
    rwa [←pow_mul,Nat.mul_comm s p]
  have hp₂ : p≠2 := by rintro rfl; exact neighboring_product_ne_square m (y^s) hpow
  have hp₃ : p≠3 := by rintro rfl; exact neighboring_product_ne_cube_unconditional m (y^s) hpow
  have h₅ : 5 ≤ p := by by_contra! h; interval_cases p <;> norm_num at *
  have hd := neighboring_proper_power_index hp.two_le hpow
  have hm : Even m := by obtain ⟨t,ht⟩ := hd; exact even_iff_two_dvd.mpr (by omega)
  have hz := lucasFibonacciSum_mul_lowerNeighbor m
  have hcast : (lucasFibonacciSum (m+2):ℤ)*lowerNeighborAtAddTwo m = ((y^s:ℕ):ℤ)^p := by
    exact_mod_cast hpow
  rw [hm.neg_one_pow,hcast] at hz
  by_contra! hu
  apply HosoyaAuxiliaryPrime.fib_small_prime_power_excluded hp h₅ hu
    (by omega : 0 < m + 2) hd ((y^s:ℕ):ℤ)
  linarith

/-- The remaining prime exponent in the exact product criterion is at least 101. -/
theorem neighboring_proper_power_large_exponent (m : ℕ) :
    (∃ y k : ℕ, 2 ≤ k ∧ lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m=y^k) ↔
    6 ∣ m+2 ∧ ∃ p y : ℕ, p.Prime ∧ 101 ≤ p ∧ y^p+1=11*(Nat.fib (m+2))^2 := by
  rw [neighboring_proper_power_iff]
  constructor
  · rintro ⟨hd,p,y,hp,h₅,he⟩
    refine ⟨hd,p,y,hp,?_,he⟩
    by_contra! hu
    exact HosoyaAuxiliaryPrime.fib_small_prime_power_excluded hp h₅ hu
      (by omega : 0 < m + 2) hd y (by exact_mod_cast he)
  · rintro ⟨hd,p,y,hp,hp',he⟩
    exact ⟨hd,p,y,hp,by omega,he⟩

#print axioms neighboring_power_prime_divisor
#print axioms neighboring_proper_power_large_exponent

end Arxiv.«2211.10788»
