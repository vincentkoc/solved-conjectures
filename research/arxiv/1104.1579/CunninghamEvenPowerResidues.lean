import CunninghamOddPowerFactorCriterion

/-! The first three coefficients determine exactly when two nonunit constants
are compatible with an even prime-power constant and its negative linear term. -/

namespace CunninghamChain
open Polynomial

/-- For the prescribed three coefficients, a splitting into two nonunit constants
exists exactly when the negative quadratic coefficient is a square modulo p^r. -/
theorem split_three_coefficients_iff {p r : ℕ} (hp : p.Prime) (hr : 0<r)
    (ε : ℤ) (hε : ¬(p:ℤ) ∣ ε) :
    (∃ A B : ℤ[X], (A*B).coeff 0=((p^r:ℕ):ℤ)^2 ∧
      (A*B).coeff 1= -((p^r:ℕ):ℤ)^2 ∧ (A*B).coeff 2=ε ∧
      ¬IsUnit (A.coeff 0) ∧ ¬IsUnit (B.coeff 0)) ↔
      ∃ u : ℤ, ((p^r:ℕ):ℤ) ∣ u^2+ε := by
  let q : ℤ := (p^r:ℕ)
  have pos : 0 < q := by dsimp [q]; exact_mod_cast pow_pos hp.pos r
  constructor
  · rintro ⟨A,B,c,l,b,ha,hb⟩
    have ab := factor_constants_natAbs_eq (e:=r+r) hp A B
      (by simp [c,pow_add,pow_two,Int.natAbs_mul]) (by simp [c,l]) (by rwa [b]) ha hb
    change (A*B).coeff 0=q^2 at c
    change (A*B).coeff 1= -q^2 at l
    rw [mul_coeff_zero] at c
    rw [mul_coeff_one] at l
    rw [coeff_two_product] at b
    have eq : A.coeff 0=B.coeff 0 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (Int.natAbs_eq_iff_sq_eq.mp ab) with e|e
      · exact e
      · rw [e] at c
        nlinarith [sq_nonneg (B.coeff 0),sq_pos_of_pos pos]
    rw [←eq] at c l b
    have signs : A.coeff 0=q ∨ A.coeff 0= -q :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa [pow_two] using c)
    have nz : A.coeff 0 ≠ 0 := by rcases signs with h|h <;> omega
    have sum : A.coeff 1+B.coeff 1 = -A.coeff 0 := by
      apply mul_left_cancel₀ nz
      nlinarith
    have dv : A.coeff 0 ∣ A.coeff 1^2+ε := by
      refine ⟨B.coeff 2+A.coeff 2-A.coeff 1,?_⟩
      linear_combination -b + A.coeff 1 * sum
    refine ⟨A.coeff 1,?_⟩
    rcases signs with h|h <;> simpa [h,q] using dv
  · rintro ⟨u,v,h⟩
    change u^2+ε=q*v at h
    let A : ℤ[X] := C q+C u*X
    let B : ℤ[X] := C q+C (-q-u)*X+C (v+u)*X^2
    have nu : ¬IsUnit q := by
      rw [Int.isUnit_iff_natAbs_eq]
      simpa [q] using (one_lt_pow₀ hp.one_lt hr.ne').ne'
    have cast_q : (p:ℤ)^r=q := by simp [q]
    refine ⟨A,B,?_,?_,?_,?_,?_⟩
    all_goals simp only [A,B,mul_coeff_zero,mul_coeff_one,coeff_two_product,coeff_add,
      coeff_C_mul,coeff_C,coeff_X,coeff_X_pow]
    all_goals norm_num
    · rw [cast_q]; ring
    · rw [cast_q]; ring
    · linear_combination -h
    · exact nu
    · exact nu

private lemma neg_one_square_at_divisor {u : ℤ} {w q : ℕ} (h : w∣q)
    (sq : (q:ℤ) ∣ u^2+1) : (u : ZMod w)^2= -1 := by
  have z := (ZMod.intCast_zmod_eq_zero_iff_dvd (u^2+1) w).mpr
    ((show (w:ℤ) ∣ (q:ℤ) by exact_mod_cast h).trans sq)
  push_cast at z
  linear_combination z

/-- Lift a root of −1 from an odd modulus p to each of its powers. -/
private lemma lift_neg_one {p c : ℤ} (odd : 2*c=p+1) (base : ∃ u : ℤ, p∣u^2+1)
    (r : ℕ) : ∃ u : ℤ, p^(r+1)∣u^2+1 := by
  induction r with
  | zero => simpa using base
  | succ r ih =>
    obtain ⟨u,w,hw⟩ := ih
    obtain ⟨z,hz⟩ := (dvd_pow_self p (Nat.succ_ne_zero r)).trans (show p^(r+1)∣u^2+1 from ⟨w,hw⟩)
    refine ⟨u*(1+c*(u^2+1)),w*(-1+z*(2*c+c^2*u^2)),?_⟩
    calc (u*(1+c*(u^2+1)))^2+1 = (u^2+1)*(1-2*c+(u^2+1)*(2*c+c^2*u^2)) := by ring
         _ = (p^(r+1)*w)*(-p+p*z*(2*c+c^2*u^2)) := by
           exact congrArg₂ (·*·) hw (by rw [hz,show 1-2*c= -p by omega])
         _ = _ := by rw [pow_succ p (r+1)]; ring

/-- The plus-sign coefficient obstruction includes all even powers of primes
3 modulo 4, and all powers of two beyond the first half power. -/
theorem neg_one_at_prime_power_iff {p r : ℕ} (hp : p.Prime) (hr : 0<r) :
    (∃ u : ℤ, ((p^r:ℕ):ℤ) ∣ u^2+1) ↔ p%4=1 ∨ (p=2 ∧ r=1) := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨u,sq⟩
    rcases eq_or_ne p 2 with rfl|odd
    · right
      refine ⟨rfl,?_⟩
      by_contra ne
      have four : 4 ∣ 2^r := pow_dvd_pow 2 (by omega : 2≤r)
      exact (show ∀ x : ZMod 4, x^2≠ -1 by decide +kernel) _ (neg_one_square_at_divisor four sq)
    · have no := ZMod.mod_four_ne_three_of_sq_eq_neg_one
          (neg_one_square_at_divisor (dvd_pow_self p hr.ne') sq)
      have par := hp.odd_of_ne_two odd
      obtain ⟨j,hj⟩ := par
      left
      omega
  · rintro (split|⟨rfl,rfl⟩)
    · obtain ⟨x,hx⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (show p%4≠3 by omega)
      obtain ⟨u,rfl⟩ := ZMod.intCast_surjective x
      have root : (p:ℤ) ∣ u^2+1 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (by
        push_cast
        rw [pow_two,←hx]
        ring)
      obtain ⟨j,hj⟩ := hp.odd_of_ne_two (by omega : p≠2)
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      have odd : 2*((j:ℤ)+1)=(p:ℤ)+1 := by omega
      simpa using lift_neg_one odd ⟨u,root⟩ k
    · exact ⟨1,by decide⟩

#print axioms neg_one_at_prime_power_iff

#print axioms split_three_coefficients_iff

end CunninghamChain
