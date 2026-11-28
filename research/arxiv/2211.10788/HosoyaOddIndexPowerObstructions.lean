import HosoyaOddIndexPowerSieve
import LucasFibonacciSquareValues

/-! Prime exponents of proper powers on individual odd-index diagonals and
the negative Pell equation attached to those powers. -/

namespace Arxiv.«2211.10788».OddIndexPowers

private theorem upper_value (n : ℕ) : value false n = (lucasFibonacciSum n : ℤ) := by
  simp [value, lucasFibonacciSum, Nat.fib_add_two]
  ring

private theorem lower_value (m : ℕ) : value true (m+2) = (lowerNeighborAtAddTwo m : ℤ) := by
  simp only [value, if_true, lowerNeighborAtAddTwo, Nat.fib_add_two, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

private theorem small_power_index {k p n t : ℕ} (lower : Bool) (h : value lower n = (t : ℤ)^k)
    (hk : p ∣ k) (hp : p.Prime) (hn : Odd n) : p = 2 ∨ 101 ≤ p := by
  by_contra! hh
  obtain ⟨a, rfl⟩ := hk
  have h' : value lower n = ((t:ℤ)^a)^p := by rwa [← pow_mul, Nat.mul_comm a p]
  exact odd_index_not_small_prime_power lower hp (by have := hp.two_le; omega) (by omega) hn _ h'

/-- The only small prime exponent on an odd upper index is 2, at indices 1
and 3. The statement allows an arbitrary natural base and a composite exponent. -/
theorem upper_odd_exponent_obstruction {n t k p : ℕ} (hn : Odd n)
    (he : lucasFibonacciSum n = t^k) (hp : p.Prime) (hk : p ∣ k) :
    (p = 2 ∧ (n = 1 ∨ n = 3)) ∨ 101 ≤ p := by
  have hz : value false n = (t:ℤ)^k := by rw [upper_value, he, Nat.cast_pow]
  rcases small_power_index false hz hk hp hn with rfl | h
  · obtain ⟨a, rfl⟩ := hk
    have hs : IsSquare (lucasFibonacciSum n) := ⟨t^a, by rw [he, two_mul, pow_add]⟩
    have hi := (lucasFibonacciSum_isSquare_iff n).mp hs
    exact Or.inl ⟨rfl, hi.resolve_left hn.pos.ne'⟩
  · exact Or.inr h

/-- On the lower diagonal at odd physical indices m+2, the only small prime
exponent is 2, at physical index 9. -/
theorem lower_odd_exponent_obstruction {m t k p : ℕ} (hn : Odd (m+2))
    (he : lowerNeighborAtAddTwo m = t^k) (hp : p.Prime) (hk : p ∣ k) :
    (p = 2 ∧ m+2 = 9) ∨ 101 ≤ p := by
  have hz : value true (m+2) = (t:ℤ)^k := by rw [lower_value, he, Nat.cast_pow]
  rcases small_power_index true hz hk hp hn with rfl | h
  · obtain ⟨a, rfl⟩ := hk
    have hs : IsSquare (lowerNeighborAtAddTwo m) := ⟨t^a, by rw [he, two_mul, pow_add]⟩
    have hi := (lowerNeighbor_isSquare_iff m).mp hs
    exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr h

private theorem even_companion (lower : Bool) {n : ℕ} (hn : Even n) :
    ∃ z : ℤ, z^2 = 5*(value lower n)^2+44 := by
  have h := fib_pair_norm n
  rw [hn.neg_one_pow] at h
  cases lower
  · refine ⟨7*(Nat.fib (n+1) : ℤ)-Nat.fib n, ?_⟩
    simp only [value, Bool.false_eq_true, if_false]
    linear_combination 44*h
  · refine ⟨7*(Nat.fib (n+1) : ℤ)-6*Nat.fib n, ?_⟩
    simp only [value, if_true]
    linear_combination 44*h

private theorem common_pell_signs {x z b : ℕ}
    (hx : x^2+44=5*b^2) (hz : z^2=5*b^2+44) : b = 5 := by
  have hlt : x < z := by nlinarith
  have hx' : x < 44 := by nlinarith [Nat.mul_self_le_mul_self (show x+1 ≤ z by omega)]
  have hx₂ := Nat.mul_self_le_mul_self (show x ≤ 43 by omega)
  have hz' : z < 45 := by
    by_contra! h
    nlinarith [Nat.mul_self_le_mul_self h]
  have hb' : b < 20 := by
    by_contra! h
    nlinarith [Nat.mul_self_le_mul_self h]
  have small : ∀ i : Fin 44, ∀ j : Fin 20, i.val^2+44 = 5*j.val^2 →
      ∀ l : Fin 45, l.val^2=5*j.val^2+44 → j.val=5 := by decide
  exact small ⟨x,hx'⟩ ⟨b,hb'⟩ hx ⟨z,hz'⟩ hz

/-- For every odd prime p below 101 there are no integer solutions of
X² + 44 = 5 Y^(2p). This excludes the square-Z part of the negative quintic
equation when p = 5. -/
theorem negative_pell_prime_power_obstruction {p : ℕ} (hp : p.Prime)
    (h₃ : 3 ≤ p) (h₁₀₁ : p < 101) (x y : ℤ) : x^2+44 ≠ 5*y^(2*p) := by
  intro he
  let t := y.natAbs
  have neg : x.natAbs^2+44 = 5*(t^p)^2 := by
    zify
    rw [Int.natCast_natAbs, sq_abs, ← pow_mul, Nat.mul_comm p 2, pow_mul, sq_abs]
    simpa only [pow_mul] using he
  obtain hit := (either_diagonal_iff_pell (t^p)).mpr ⟨_, Or.inr neg⟩
  obtain ⟨lower, n, hval⟩ : ∃ (lower : Bool) (n : ℕ), value lower n = (t:ℤ)^p := by
    rcases hit with ⟨n, hn⟩ | (hh | ⟨m, hm⟩)
    · exact ⟨false,n,by rw [upper_value, ← hn, Nat.cast_pow]⟩
    · refine ⟨true,1,?_⟩
      have hh' : ((t:ℤ)^p) = 3 := by exact_mod_cast hh
      rw [hh']; decide
    · exact ⟨true,m+2,by rw [lower_value, ← hm, Nat.cast_pow]⟩
  have hn : Even n := by
    by_contra h
    exact odd_index_not_small_prime_power lower hp h₃ h₁₀₁ (Nat.not_even_iff_odd.mp h) _ hval
  obtain ⟨z,hz⟩ := even_companion lower hn
  rw [hval] at hz
  have pos : z.natAbs^2 = 5*(t^p)^2+44 := by
    zify
    rw [Int.natCast_natAbs, sq_abs]
    simpa only [t, Int.natCast_natAbs] using hz
  have ht := common_pell_signs neg pos
  by_cases h : t ≤ 1
  · interval_cases t <;> simp_all [hp.ne_zero]
  · have hh : 2^3 ≤ t^p := (Nat.pow_le_pow_left (by omega : 2 ≤ t) 3).trans
        (Nat.pow_le_pow_right (by omega : 0 < t) h₃)
    omega

/-- Song's positive quintic classification alone gives the full fifth-power
classification on both diagonals. The negative equation at square arguments
is supplied by the odd-index obstruction. -/
theorem fifth_powers_of_positive_quintic
    (positive : ∀ x z : ℕ, 0 < z → x^2 = 5*z^5+44 → z=1) (t : ℕ) :
    ((∃ n, t^5 = lucasFibonacciSum n) ∨ IsLowerNeighborValue (t^5)) ↔ t=1 := by
  constructor
  · intro hh
    obtain ⟨x, hx | hx⟩ := (either_diagonal_iff_pell (t^5)).mp hh
    · have ht : 0 < t := by
        by_contra! h
        obtain rfl := Nat.eq_zero_of_le_zero h
        norm_num at hx
        by_cases hsmall : x ≤ 6
        · nlinarith [Nat.mul_self_le_mul_self hsmall]
        · nlinarith [Nat.mul_self_le_mul_self (show 7 ≤ x by omega)]
      have h := positive x (t^2) (pow_pos ht _) (by simpa only [← pow_mul] using hx)
      nlinarith
    · exfalso
      apply negative_pell_prime_power_obstruction (p := 5) (by decide) (by decide) (by decide) (x:ℤ) (t:ℤ)
      exact_mod_cast (show x^2+44=5*t^(2*5) by simpa only [← pow_mul] using hx)
  · rintro rfl
    exact Or.inl ⟨0, by decide⟩

#print axioms fifth_powers_of_positive_quintic

#print axioms upper_odd_exponent_obstruction
#print axioms lower_odd_exponent_obstruction
#print axioms negative_pell_prime_power_obstruction

end Arxiv.«2211.10788».OddIndexPowers
