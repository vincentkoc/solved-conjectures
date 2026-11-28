import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-! One modulus detects integral powers near each bounded signed integer. -/

namespace Arxiv.«2211.10788».PowerIndex

/-- An integer passing the power test modulo four times its square is an
actual integral power. At zero the congruence simply means equality. -/
theorem integer_power_of_modEq {w t : ℤ} {k : ℕ}
    (test : w ≡ t^k [ZMOD 4*w^2]) : ∃ v : ℤ, w=v^k := by
  obtain ⟨c,hc⟩ := Int.modEq_iff_dvd.mp test
  let u := 1+4*w*c
  have cop : IsCoprime w u := ⟨-4*c,1,by dsimp [u]; ring⟩
  have prod : w*u=t^k := by dsimp [u]; linear_combination -hc
  rcases Nat.even_or_odd k with even | odd
  · have square : ∃ z : ℤ, u=z^2 ∨ u= -z^2 := by
      obtain ⟨l,hl⟩ := even
      apply Int.sq_of_isCoprime cop.symm (c:=t^l)
      rw [mul_comm,prod,hl,pow_add,pow_two]
    have unit : (u : ZMod 4)=1 := by dsimp [u]; push_cast; rw [show (4 : ZMod 4)=0 by decide]; ring
    have upos : 0 < u := by
      obtain ⟨z,h|h⟩ := square
      · have nz : u≠0 := by
          intro eq
          exact (by decide : (0 : ZMod 4) ≠ 1) (by simpa only [eq,Int.cast_zero] using unit)
        rw [h] at nz ⊢
        exact lt_of_le_of_ne (sq_nonneg z) (Ne.symm nz)
      · have excl : ∀ b : ZMod 4, -(b^2) ≠ 1 := by decide
        rw [h] at unit
        push_cast at unit
        exact False.elim (excl _ unit)
    have wn : 0 ≤ w := nonneg_of_mul_nonneg_left (prod ▸ even.pow_nonneg t) upos
    obtain ⟨v,hv⟩ := exists_associated_pow_of_mul_eq_pow' cop prod
    have abs := Int.natAbs_eq_natAbs_iff.mp (Int.associated_iff_natAbs.mp hv.symm)
    exact ⟨v,abs.elim id (fun h => by have := even.pow_nonneg v; omega)⟩
  · exact Int.eq_pow_of_mul_eq_pow_odd_left cop odd prod

/-- A single modulus works for every target of absolute value at most B
and for every positive exponent k. -/
theorem bounded_power_test (B : ℕ) {w t : ℤ} {k : ℕ} (pos : 0 < k)
    (size : w.natAbs ≤ B) (test : t^k ≡ w [ZMOD (4*B.factorial^2 : ℕ)]) :
    ∃ v : ℤ, w=v^k := by
  by_cases zero : w=0
  · exact ⟨0,by simp [zero,pos.ne']⟩
  have dv := Nat.dvd_factorial (Int.natAbs_pos.mpr zero) size
  have moddiv : (4*w^2 : ℤ) ∣ (4*B.factorial^2 : ℕ) := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa [Int.natAbs_mul,Int.natAbs_pow] using
      Nat.mul_dvd_mul_left 4 (pow_dvd_pow_of_dvd dv 2)
  exact integer_power_of_modEq (test.symm.of_dvd moddiv)

#print axioms integer_power_of_modEq
#print axioms bounded_power_test

end Arxiv.«2211.10788».PowerIndex
