import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # A cubic packing bound for a collection of quotient values -/

namespace Erdos478.QuotientSpacing

/-- A family with capacity k per gap of length k has a cubic return bound.
The mass and width may have been divided by the number of allowed quotients. -/
theorem real_capacity_bound (r w : ℝ) (hr : 0≤r) (hw : r≤w)
    (cost : ∀ h : ℕ, 1≤h → 6*h*r+h ≤ 6*w+(h:ℝ)^3) : 8*r^3≤9*w^2 := by
  by_cases small : r≤1
  · have sq := mul_self_le_mul_self hr hw
    nlinarith [mul_le_mul_of_nonneg_right small (sq_nonneg r)]
  let x := Real.sqrt (2*r)
  have sq : x^2=2*r := Real.sq_sqrt (by linarith)
  have xpos : 0≤x := Real.sqrt_nonneg _
  have large : 1≤x := by nlinarith
  let h := ⌊x+1/2⌋₊
  have hi : (h:ℝ)≤x+1/2 := Nat.floor_le (by linarith)
  have lo : x+1/2<(h:ℝ)+1 := Nat.lt_floor_add_one _
  have pos : 1≤h := by
    by_contra! hn
    have : h=0 := by omega
    rw [this,Nat.cast_zero] at lo
    linarith
  have one : (1:ℝ)≤h := by exact_mod_cast pos
  have err : (x-h)^2≤1/4 := by
    nlinarith [mul_nonneg (by linarith : 0≤1/2-(x-h)) (by linarith : 0≤1/2+(x-h))]
  have e := mul_le_mul_of_nonneg_right err (by positivity : 0≤2*x+h)
  have budget := cost h pos
  have tangent : x^3≤3*w := by nlinarith [congrArg (fun z : ℝ => h*z) sq]
  have cube := congrArg (fun z : ℝ => z^3) sq
  nlinarith [mul_self_le_mul_self (by positivity : 0≤x^3) tangent]

/-- With `C` allowed ratios and `m` distinct realizations per return,
the effective gap capacity is `C*k/m`. All quantities are integral. -/
theorem weighted_capacity_bound (R W C m : ℕ) (hC : 0<C) (hm : 0<m) (length : R≤W)
    (budget : ∀ h : ℕ, 1≤h → 6*h*(m*R)+C*h ≤ 6*(m*W)+C*h^3) :
    8*m*R^3≤9*C*W^2 := by
  have cp : (0:ℝ)<C := by exact_mod_cast hC
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have lw : (R:ℝ)≤W := by exact_mod_cast length
  let r := (m:ℝ)*R/C
  let w := (m:ℝ)*W/C
  have scaled : 8*r^3≤9*w^2 := by
    apply real_capacity_bound _ _ (show 0≤(m:ℝ)*R/C by positivity)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left lw mp.le) cp.le)
    intro h hh
    have b : 6*(h:ℝ)*(m*R)+C*h ≤ 6*(m*W)+C*h^3 := by exact_mod_cast budget h hh
    change 6*(h:ℝ)*((m:ℝ)*R/C)+h≤6*((m:ℝ)*W/C)+(h:ℝ)^3
    field_simp
    nlinarith
  dsimp [r,w] at scaled
  have result : (8:ℝ)*m*R^3≤9*C*W^2 := by
    rw [div_pow,div_pow] at scaled
    field_simp at scaled
    by_contra! bad
    have prod := mul_pos (sub_pos.mpr bad) (by positivity : 0<(m:ℝ)^2)
    nlinarith
  exact_mod_cast result

#print axioms real_capacity_bound
#print axioms weighted_capacity_bound
end Erdos478.QuotientSpacing
