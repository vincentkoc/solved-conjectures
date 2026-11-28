import Green51LogDensityWindow
import Green51CriticalWindow

/-! # Exact dimension at logarithmic shifts of the critical square-root density -/

namespace Green51GirthFrame
open Real Green51Hyperplane

/-- Offsetting the dimension in the square-root density gives the same exact value in both parities. -/
theorem shifted_critical_value {n : ℕ} (hn : 16 ≤ n) {x : ℝ}
    (low : ((n - logWidth n : ℕ) : ℝ) ≤ x) (high : x ≤ 2 * ((n / 2 : ℕ) : ℝ)) :
    Green51.guaranteedMaxCosetDim n (1 / 2 - (1 / √(2 * π)) / √x) = n - 2 := by
  have dn : logWidth n < n := lt_of_le_of_lt (Nat.sub_le ..) (Nat.log_lt_self 2 (by omega))
  let m := n - logWidth n
  have mp : 0 < m := by dsimp [m]; omega
  have xp : 0 < x := lt_of_lt_of_le (by exact_mod_cast mp) low
  have lower := Green51CriticalWindow.past_odd_layer ((m - 1) / 2) m (by omega)
  have invLower : (1 / √(2 * π)) / √x ≤ (1 / √(2 * π)) / √(m : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by exact_mod_cast mp)) (Real.sqrt_le_sqrt low)
  have smaller := even_layer_strict (n / 2)
  have upper : halfLayer (n / 2) < (1 / √(2 * π)) / √x := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr xp)).mpr
    calc
      halfLayer (n / 2)*√x ≤ √(2 * ((n / 2 : ℕ) : ℝ)) * halfLayer (n / 2) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt high) (halfLayer_pos _).le
      _ < _ := smaller
  apply logarithmic_interval hn
  · change 1 / 2 - halfLayer ((m - 1) / 2)<_
    linarith
  · change _ ≤ 1 / 2 - halfLayer (n / 2)
    linarith

end Green51GirthFrame
#print axioms Green51GirthFrame.shifted_critical_value

namespace Green51GirthFrame
open Filter Real
private theorem floor_log_top :
    Tendsto (fun n : ℕ => ((Nat.log 2 n : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop.2
  intro a
  filter_upwards [eventually_ge_atTop (2 ^ a : ℕ)] with n hn
  exact Nat.le_log_of_pow_le (by decide) hn

/-- The dimension allowance eventually exceeds any fixed fraction of the base-two logarithm. -/
theorem log_width_eventually {c : ℝ} (hc : 0 < c) (small : c < 1) :
    ∀ᶠ n : ℕ in atTop, c * logb 2 n ≤ logWidth n := by
  let e := (1 - c) / 4
  have ep : 0 < e := by dsimp [e]; linarith
  have top : Tendsto (fun n : ℕ => (((Nat.log 2 n) + 2 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => Nat.cast_le.mpr (Nat.le_add_right _ 2)) floor_log_top
  have tiny := (Real.isLittleO_logb_id_atTop (b := 2)).bound ep
  filter_upwards [top.eventually tiny, floor_log_top.eventually_ge_atTop (2 / e)]
    with n bound large
  let k := Nat.log 2 n
  let j := Nat.log 2 (k + 2)
  have kl : 2 ≤ (k : ℝ) * e := (div_le_iff₀ ep).mp large
  have logj := Real.natLog_le_logb (k + 2) 2
  have cmp : (j : ℝ) ≤ e * ((k : ℝ) + 2) := by
    change ‖logb 2 ((k + 2 : ℕ) : ℝ)‖ ≤ e * ‖((k + 2 : ℕ) : ℝ)‖ at bound
    have rhs := le_abs_self (logb 2 ((k + 2 : ℕ) : ℝ))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (k + 2) : 0 ≤ ((k + 2 : ℕ) : ℝ))] at bound
    push_cast at bound rhs logj
    exact logj.trans (rhs.trans bound)
  have frac : logb 2 n < (k : ℝ) + 1 := by
    have bound := Nat.lt_floor_add_one (logb (2 : ℕ) (n : ℝ))
    rw [Real.natFloor_logb_natCast] at bound
    simpa only [Nat.cast_ofNat] using bound
  have sub : (k : ℝ) ≤ (logWidth n : ℝ) + (j : ℝ) := by
    exact_mod_cast (show k ≤ (k - j) + j by omega)
  have mul := mul_le_mul_of_nonneg_left frac.le hc.le
  dsimp [e] at cmp kl
  nlinarith

/-- Any fixed fraction of the base-two logarithm gives the exact shifted square-root density. -/
theorem logarithmic_shift {c : ℝ} (hc : 0 < c) (small : c < 1) :
    ∀ᶠ n : ℕ in atTop, Green51.guaranteedMaxCosetDim n
      (1 / 2 - (1 / √(2 * π)) / √((n : ℝ) - c * logb 2 n)) = n - 2 := by
  filter_upwards [log_width_eventually hc small, floor_log_top.eventually_ge_atTop (1 / c),
    eventually_ge_atTop (16 : ℕ)] with n width large hn
  have start : 1 ≤ c * logb 2 n := by
    have t := (div_le_iff₀ hc).mp (large.trans (Real.natLog_le_logb n 2))
    simpa only [Nat.cast_ofNat, mul_comm] using t
  have dn : logWidth n ≤ n := (Nat.sub_le ..).trans (Nat.log_le_self 2 n)
  apply shifted_critical_value hn
  · rw [Nat.cast_sub dn]; linarith
  · have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    linarith
end Green51GirthFrame
#print axioms Green51GirthFrame.log_width_eventually
#print axioms Green51GirthFrame.logarithmic_shift
