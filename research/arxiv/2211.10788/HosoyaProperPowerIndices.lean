import HosoyaOddNormPowers
import HosoyaNeighborCubesUnconditional

/-! Proper-power obstruction on the two neighboring Fibonacci–Lucas diagonals. -/

namespace Arxiv.«2211.10788»

private lemma three_dvd_of_even_fib {n : ℕ} (he : 2 ∣ Nat.fib n) : 3 ∣ n := by
  by_contra hn
  have hc := Nat.prime_three.coprime_iff_not_dvd.mpr hn
  have hd := Nat.dvd_gcd (by decide : 2 ∣ Nat.fib 3) he
  rw [←Nat.fib_gcd,hc.gcd_eq_one] at hd
  exact (by decide : ¬2 ∣ Nat.fib 1) hd

private lemma even_of_minus_power {f y : ℤ} {k : ℕ} (hk : 2 ≤ k)
    (he : y^k=11*f^2-1) : Even f := by
  by_contra h
  obtain ⟨s,hs⟩ := Int.not_even_iff_odd.mp h
  have h₂ : (2:ℤ) ∣ y^k := ⟨22*s^2+22*s+5,by rw [he,hs]; ring⟩
  have h₄ : (4:ℤ) ∣ y^k := pow_dvd_pow_of_dvd_of_le (Int.prime_two.dvd_of_dvd_pow h₂) hk
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (y^k) 4).mpr h₄
  rw [he,hs] at hz
  push_cast at hz
  exact (by decide : ∀ s : ZMod 4, 11*(2*s+1)^2-1 ≠ 0) _ hz

/-- Any proper power in the neighboring product must occur at a physical index
divisible by six. This holds unconditionally and simultaneously for all exponents. -/
theorem neighboring_proper_power_index {m y k : ℕ} (hk : 2 ≤ k)
    (he : lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m=y^k) : 6 ∣ m+2 := by
  have hz := lucasFibonacciSum_mul_lowerNeighbor m
  have hcast : (lucasFibonacciSum (m+2):ℤ)*lowerNeighborAtAddTwo m=(y:ℤ)^k := by exact_mod_cast he
  rw [hcast] at hz
  rcases Nat.even_or_odd k with hke|hko
  · obtain ⟨s,hs⟩ := hke
    exact (neighboring_product_ne_square m (y^s) (by rwa [←pow_mul,show s*2=k by omega])).elim
  rcases Nat.even_or_odd m with hme|hmo
  · rw [hme.neg_one_pow] at hz
    have hf := even_of_minus_power hk hz
    have hd := three_dvd_of_even_fib (show 2 ∣ Nat.fib (m+2) by exact_mod_cast even_iff_two_dvd.mp hf)
    obtain ⟨s,hs⟩ := hme
    omega
  · rw [hmo.neg_one_pow] at hz
    have hf := HosoyaOddNorm.odd_power_eq_one_add_eleven_square (by omega : 1<k) hko
      (show (y:ℤ)^k=1+11*(Nat.fib (m+2):ℤ)^2 by linarith)
    have hp := Nat.fib_pos.mpr (show 0 < m+2 by omega)
    omega

/-- The entire remaining product question is equivalent to the single negative
shift of eleven times the Fibonacci square, at multiples of six and prime exponents ≥5. -/
theorem neighboring_proper_power_iff (m : ℕ) :
    (∃ y k : ℕ, 2 ≤ k ∧ lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m=y^k) ↔
    6 ∣ m+2 ∧ ∃ p y : ℕ, p.Prime ∧ 5 ≤ p ∧ y^p+1=11*(Nat.fib (m+2))^2 := by
  constructor
  · rintro ⟨y,k,hk,he⟩
    have h₆ := neighboring_proper_power_index hk he
    have hme : Even m := by obtain ⟨t,ht⟩ := h₆; exact even_iff_two_dvd.mpr (by omega)
    obtain ⟨p,hp,s,hs⟩ := Nat.exists_prime_and_dvd (show k≠1 by omega)
    have hpow : lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m=(y^s)^p := by
      rwa [←pow_mul,Nat.mul_comm s p,←hs]
    have hp₂ : p≠2 := by rintro rfl; exact neighboring_product_ne_square m (y^s) hpow
    have hp₃ : p≠3 := by rintro rfl; exact neighboring_product_ne_cube_unconditional m (y^s) hpow
    have hp₅ : 5 ≤ p := by by_contra! h; interval_cases p <;> norm_num at *
    refine ⟨h₆,p,y^s,hp,hp₅,?_⟩
    have hz := lucasFibonacciSum_mul_lowerNeighbor m
    rw [hme.neg_one_pow] at hz
    have hz' : (lucasFibonacciSum (m+2):ℤ)*lowerNeighborAtAddTwo m=((y^s:ℕ):ℤ)^p := by exact_mod_cast hpow
    exact_mod_cast (show ((y^s:ℕ):ℤ)^p+1=11*(Nat.fib (m+2):ℤ)^2 by linarith)
  · rintro ⟨h₆,p,y,hp,hp₅,he⟩
    have hme : Even m := by obtain ⟨t,ht⟩ := h₆; exact even_iff_two_dvd.mpr (by omega)
    have hz := lucasFibonacciSum_mul_lowerNeighbor m
    rw [hme.neg_one_pow] at hz
    have hz' : (y:ℤ)^p+1=11*(Nat.fib (m+2):ℤ)^2 := by exact_mod_cast he
    refine ⟨y,p,hp.two_le,?_⟩
    exact_mod_cast (show (lucasFibonacciSum (m+2):ℤ)*lowerNeighborAtAddTwo m=(y:ℤ)^p by linarith)

#print axioms neighboring_proper_power_index
#print axioms neighboring_proper_power_iff

end Arxiv.«2211.10788»
