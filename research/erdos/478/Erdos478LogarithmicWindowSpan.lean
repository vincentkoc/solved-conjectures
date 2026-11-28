import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # The square-root logarithmic span for factorial collision spacing -/

namespace Erdos478.LocalSpacing
open Filter Real Topology

/-- An explicit integral span growing with the observation prime. -/
noncomputable def logSpan (c : ℝ) (p : ℕ) : ℕ := ⌊c*√(log p / log (log p))⌋₊

private theorem log_ratio_grows : Tendsto (fun x : ℝ => x / log x) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  let b := max M 1
  have hb : 0<b := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  filter_upwards [Real.isLittleO_log_id_atTop.bound (inv_pos.mpr hb),eventually_gt_atTop (1:ℝ)] with x h hx
  have hlog := Real.log_pos hx
  have hh : log x≤b⁻¹*x := by simpa [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos (lt_trans zero_lt_one hx)] using h
  exact (le_max_left ..).trans ((le_div_iff₀ hlog).mpr (by
    calc b*log x≤b*(b⁻¹*x) := mul_le_mul_of_nonneg_left hh hb.le
         _=x := by field_simp))

theorem logSpan_grows (c : ℝ) (hc : 0<c) : Tendsto (logSpan c) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  exact (Real.tendsto_sqrt_atTop.comp (log_ratio_grows.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).const_mul_atTop hc

private theorem log_cut {p H : ℕ} {c : ℝ} (hc : 0≤c) (hc2 : c^2≤2)
    (L : 25≤log p) (T : 8≤log (log p)) (hH : (H:ℝ)≤c*√(log p/log (log p))) :
    (H+2)^(H^2)<p := by
  let x := log p
  let y := log x
  have hx : 0<x := by change 0<log p; linarith
  have hy : 0<y := by change 0<log (log p); linarith
  have sq : (H:ℝ)^2≤c^2*(x/y) := by
    simpa only [mul_pow,Real.sq_sqrt (div_pos hx hy).le] using
      (sq_le_sq' (le_trans (neg_nonpos.mpr (mul_nonneg hc (Real.sqrt_nonneg _)) : -(c*√(x/y))≤0) (Nat.cast_nonneg H)) hH)
  have bound : (H:ℝ)^2≤(2*x)/y := by
    simpa only [mul_div_assoc] using sq.trans (mul_le_mul_of_nonneg_right hc2 (div_pos hx hy).le)
  have main := (le_div_iff₀ hy).mp bound
  have half : 4*(H:ℝ)^2≤x := by
    have ty : 8≤y := T
    nlinarith only [main,mul_le_mul_of_nonneg_left ty (sq_nonneg (H:ℝ))]
  have hs := Real.sq_sqrt hx.le
  have rt : 4<√x := by
    have lx : 25≤x := L
    nlinarith [Real.sqrt_nonneg x]
  have hH' : 2*(H:ℝ)≤√x := by nlinarith [Real.sqrt_nonneg x,Nat.cast_nonneg (α:=ℝ) H]
  have rad : (H:ℝ)+2<√x := by linarith
  have lograd := Real.log_lt_log (by positivity : 0<(H:ℝ)+2) rad
  rw [Real.log_sqrt hx.le] at lograd
  have lg : ((H:ℝ)^2)*log ((H:ℝ)+2)<x := by
    calc
      _≤(2*x/y)*log ((H:ℝ)+2) := mul_le_mul_of_nonneg_right bound (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) H]))
      _<(2*x/y)*(y/2) := mul_lt_mul_of_pos_left lograd (by positivity)
      _=x := by field_simp
  have pp : (0:ℝ)<p := by by_contra! h; have : (p:ℝ)=0 := le_antisymm h (Nat.cast_nonneg _); norm_num [this] at L
  have h := (Real.log_lt_log_iff (by positivity : 0<((H:ℝ)+2)^(H^2)) pp).mp (by
    rw [Real.log_pow]; exact_mod_cast lg)
  exact_mod_cast h

theorem logSpan_cut (c : ℝ) (hc : 0≤c) (hc2 : c^2≤2) :
    ∀ᶠ p : ℕ in atTop, (logSpan c p+2)^(logSpan c p^2)<p := by
  have lim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [lim.eventually_ge_atTop 25,(Real.tendsto_log_atTop.comp lim).eventually_ge_atTop 8] with p L T
  apply log_cut hc hc2 L T
  apply Nat.floor_le
  exact mul_nonneg hc (Real.sqrt_nonneg _)

#print axioms logSpan
#print axioms logSpan_grows
#print axioms logSpan_cut
end Erdos478.LocalSpacing
