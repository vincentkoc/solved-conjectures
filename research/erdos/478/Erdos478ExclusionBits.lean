import Erdos478SievedSchurPrime
import Erdos478ResolventScale

/-!
# The bit cost of excluding more prime divisors

In the sieved Schur bound an extra factor of size at most a double
exponential increases the bit parameter by its double logarithm plus three.
-/

namespace Erdos478.EffectiveResolvent

theorem sieveBits_extra {D B C b l : ℕ} (hB : sieveBits D B ≤ b) (hC : C ≤ 2^(2^l)) :
    sieveBits D (C*B) ≤ b+l+3 := by
  have base : max (D+1) (Nat.log 2 B+1) ≤ 2^b :=
    (Nat.le_pow_clog (by decide : 1<2) _).trans (Nat.pow_le_pow_right (by decide) hB)
  have sizeB : B ≤ 2^(Nat.log 2 B+1) := (Nat.lt_pow_succ_log_self (by decide : 1<2) B).le
  have bound := mul_bound hC sizeB
  have logBound := (Nat.log_mono_right (b := 2) bound).trans_eq (Nat.log_pow (by decide) _)
  have hsum := add_bound (le_refl (2^l : ℕ)) ((le_max_right _ _).trans base)
  apply Nat.clog_le_of_le_pow
  apply max_le
  · exact ((le_max_left _ _).trans base).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (add_bound (logBound.trans hsum) (by decide : 1≤(2:ℕ)^0)).trans
      (Nat.pow_le_pow_right (by decide) (by omega))

#print axioms sieveBits_extra

end Erdos478.EffectiveResolvent
