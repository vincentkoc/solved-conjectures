import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # The cubic bounds obtained by rounding a real optimizer to an integer -/

namespace Erdos478.ReturnConcentration

private theorem nearest {x : ℝ} (hx : 1 ≤ x) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ x + 1/2 ∧ x - 1/2 ≤ n := by
  let n := ⌊x + 1/2⌋₊
  have hn : (n : ℝ) ≤ x + 1/2 := Nat.floor_le (by linarith)
  have hn' : x + 1/2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨n, ?_, hn, by linarith⟩
  by_contra! hz
  have : n = 0 := by omega
  rw [this, Nat.cast_zero] at hn'
  linarith

/-- An integer tangent bound for unrestricted degree capacities. -/
theorem unrestricted_cubic {R W : ℕ}
    (budget : ∀ h : ℕ, 1 ≤ h → 6*h*(R+1)+h ≤ 6*(W+1)+h^3) :
    8*(R+1)^3 ≤ 9*(W+1)^2 := by
  by_cases hz : R = 0
  · subst R
    nlinarith [Nat.zero_le W, Nat.zero_le (W^2)]
  have hr : (1:ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  let x := Real.sqrt (2*((R:ℝ)+1))
  have sq : x^2 = 2*((R:ℝ)+1) := Real.sq_sqrt (by positivity)
  have xp : 0 ≤ x := Real.sqrt_nonneg _
  have hx : 2 ≤ x := by nlinarith
  obtain ⟨h,hn,hu,hl⟩ := nearest (by linarith : 1 ≤ x)
  have err : (x-h)^2 ≤ 1/4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ (1/2:ℝ) - (x-h)) (by linarith : 0 ≤ (1/2:ℝ)+(x-h))]
  have cost := mul_le_mul_of_nonneg_right err (by positivity : 0 ≤ 2*x+h)
  have b : 6*(h:ℝ)*(R+1)+h ≤ 6*(W+1)+h^3 := by exact_mod_cast budget h hn
  have tangent : x^3 ≤ 3*((W:ℝ)+1) := by nlinarith [congrArg (fun v : ℝ => (h:ℝ)*v) sq]
  have cubed := congrArg (fun v : ℝ => v^3) sq
  have squared := mul_self_le_mul_self (by positivity : 0 ≤ x^3) tangent
  exact_mod_cast (show 8*((R:ℝ)+1)^3 ≤ 9*((W:ℝ)+1)^2 by nlinarith)

/-- Halving every even gap capacity gives the smaller leading constant. -/
theorem reflected_cubic {R W : ℕ}
    (budget : ∀ t : ℕ, 1 ≤ t → 2*t*(R+1) ≤ W+t^3+1) :
    32*R^3 ≤ 27*(W+1)^2 := by
  rcases Nat.eq_zero_or_pos R with rfl | hp
  · simp
  by_cases one : R = 1
  · subst R
    have b := budget 1 (by decide)
    norm_num at b ⊢
    nlinarith [Nat.zero_le (W^2)]
  have hr : (2:ℝ) ≤ R := by exact_mod_cast (show 2 ≤ R by omega)
  let x := Real.sqrt (2*(R:ℝ)/3)
  have sq : x^2 = 2*(R:ℝ)/3 := Real.sq_sqrt (by positivity)
  have xp : 0 ≤ x := Real.sqrt_nonneg _
  have hx : 1 ≤ x := by nlinarith
  obtain ⟨t,hn,hu,hl⟩ := nearest hx
  have ht : (1:ℝ) ≤ t := by exact_mod_cast hn
  have err : (x-t)^2 ≤ 1/4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ (1/2:ℝ) - (x-t)) (by linarith : 0 ≤ (1/2:ℝ)+(x-t))]
  have cost := mul_le_mul_of_nonneg_right err (by positivity : 0 ≤ 2*x+t)
  have b : 2*(t:ℝ)*(R+1) ≤ W+t^3+1 := by exact_mod_cast budget t hn
  have tangent : 2*x^3 ≤ (W:ℝ)+1 := by nlinarith [congrArg (fun v : ℝ => (t:ℝ)*v) sq]
  have cubed := congrArg (fun v : ℝ => v^3) sq
  have squared := mul_self_le_mul_self (by positivity : 0 ≤ 2*x^3) tangent
  exact_mod_cast (show 32*(R:ℝ)^3 ≤ 27*((W:ℝ)+1)^2 by nlinarith)

#print axioms unrestricted_cubic
#print axioms reflected_cubic

end Erdos478.ReturnConcentration
