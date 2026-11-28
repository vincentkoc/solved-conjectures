import Mathlib

/-! Parity restrictions from two different moduli of a Jones factorization. -/

namespace CunninghamChain.JonesSplitParity

/-- An odd unit distinct from one modulo a power of two has even multiplicative order. -/
theorem even_exponent_mod_two_power {u k e : ℕ} (hu : Odd u)
    (hne : (u : ZMod (2^(k+1))) ≠ 1) (hpow : (u : ZMod (2^(k+1)))^e=1) : Even e := by
  by_contra hn
  have he := Nat.not_even_iff_odd.mp hn
  have hc : u.Coprime (2^(k+1)) := (Nat.coprime_two_right.mpr hu).pow_right _
  have hf := Nat.ModEq.pow_totient hc
  rw [Nat.totient_prime_pow_succ Nat.prime_two] at hf
  have ht : (u:ZMod (2^(k+1)))^(2^k)=1 := by
    simpa using (ZMod.natCast_eq_natCast_iff ..).mpr hf
  have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht) (orderOf_dvd_of_pow_eq_one hpow)
  rw [((Nat.coprime_two_left.mpr he).pow_left k).gcd_eq_one] at hh
  exact hne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hh))

/-- If one complementary constant squares to −1 modulo a divisor greater than two on the
opposite side of a factorization, the degree must be even. -/
theorem even_exponent_of_square_eq_neg_one {p j : ℕ} (hodd : 2 < p)
    (a : ZMod p) (hs : a^2 = -1) (hh : (a^2)^j=1) : Even j := by
  by_contra hn
  have h := Nat.not_even_iff_odd.mp hn
  rw [hs,h.neg_one_pow] at hh
  have hz : (2 : ZMod p) = 0 := by linear_combination -hh
  exact Nat.not_dvd_of_pos_of_lt (by decide) hodd ((ZMod.natCast_eq_zero_iff 2 p).mp hz)

/-- A nontrivial odd residue modulo a power of two dividing m−1 forces j+1
even, while a fourth root of unity modulo a prime of the complement forces j
even. These two factor congruences cannot hold together. -/
theorem incompatible_parities {m u v p k j : ℕ} (hM : 2^(k+1) ∣ m-1)
    (hp2 : 2<p) (hpv : p ∣ v) (hu : Odd u)
    (hneq : (u:ZMod (2^(k+1)))≠1) (hs : (u:ZMod p)^2 = -1)
    (hc : (u:ZMod (m-1))^(j+1)=1) (ht : ((u:ZMod v)^2)^j=1) : False := by
  have hc' := congrArg (ZMod.castHom hM (ZMod (2^(k+1)))) hc
  have ht' := congrArg (ZMod.castHom hpv (ZMod p)) ht
  simp only [map_pow, map_natCast, map_one] at hc' ht'
  have he := even_exponent_mod_two_power hu hneq hc'
  have hj := even_exponent_of_square_eq_neg_one hp2 (u:ZMod p) hs ht'
  obtain ⟨s,hs⟩ := he
  obtain ⟨t,ht⟩ := hj
  omega

#print axioms incompatible_parities

end CunninghamChain.JonesSplitParity
