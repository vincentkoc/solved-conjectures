import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Inverting the explicit double-logarithmic prime bound

For fixed positive offsets, `T ≤ (x+a) log(x+b) + (ε/4)x` forces
`T ≤ x (log T - log log T + ε)` when both parameters are large.
-/

namespace Erdos478.SchurSieve
open Real Filter

private theorem sublinear_log (c : ℝ) (hc : 0<c) :
    ∀ᶠ z : ℝ in atTop, log z ≤ c*z := by
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc,eventually_ge_atTop (0:ℝ)] with z hz hz0
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs,abs_of_nonneg hz0] using hz)

/-- The additive error in the denominator can be arbitrarily small. -/
theorem invert_shifted_ceiling (a b ε : ℝ) (ha : 0<a) (hb : 0<b) (hε : 0<ε) :
    ∃ X Y : ℝ, ∀ x T : ℝ, X≤x → Y≤log T → 0<T → T ≤ (x+a)*log (x+b)+(ε/4)*x →
      T ≤ x*(log T-log (log T)+ε) := by
  let η := ε/4
  have hη : 0<η := by dsimp [η]; positivity
  have hA : 0<1+η := by positivity
  obtain ⟨M,hM⟩ := eventually_atTop.mp (sublinear_log (η/(2*a)) (by positivity))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (sublinear_log (η/(1+η)) (by positivity))
  refine ⟨max (max b M) (b/η),max 1 N,?_⟩
  intro x T hX hY hT hceil
  let y := log T
  obtain ⟨hxM',h4η⟩ := max_le_iff.mp hX
  obtain ⟨hx4,hxM⟩ := max_le_iff.mp hxM'
  obtain ⟨hy1,hyN⟩ := max_le_iff.mp hY
  have hx : 0<x := by linarith
  have hy : 0<y := by dsimp [y]; linarith
  have h4 : b ≤ η*x := by simpa [mul_comm] using (div_le_iff₀ hη).mp h4η
  have hslack : a*log (x+b) ≤ x*η := by
    calc
      _ ≤ a*((η/(2*a))*(x+b)) := mul_le_mul_of_nonneg_left (hM _ (by linarith)) ha.le
      _ = (η/2)*(x+b) := by field_simp
      _ ≤ _ := by nlinarith only [mul_nonneg (sub_nonneg.mpr hx4) hη.le]
  change T ≤ x*(y-log y+ε)
  by_cases h : T ≤ x*y/(1+η)
  · have hlog := hN y hyN
    have hsmall : y/(1+η) ≤ y-log y := by
      have he : y/(1+η)+η/(1+η)*y=y := by field_simp
      linarith
    calc
      T ≤ x*(y/(1+η)) := by simpa only [mul_div_assoc] using h
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hx.le
  · have hxy : x ≤ (1+η)*T/y := (le_div_iff₀ hy).mpr (by
      have := (div_lt_iff₀ hA).mp (lt_of_not_ge h)
      linarith only [this,mul_comm T (1+η)])
    have hxlim : x+b ≤ (1+η)^2*T/y := by
      calc
        x+b ≤ (1+η)*x := by linarith
        _ ≤ (1+η)*((1+η)*T/y) := mul_le_mul_of_nonneg_left hxy hA.le
        _ = _ := by ring
    have hlog := log_le_log (by positivity) hxlim
    rw [log_div (by positivity) hy.ne', log_mul (pow_ne_zero _ hA.ne') hT.ne', log_pow] at hlog
    have hηlog := log_le_sub_one_of_pos hA
    have hb : log (x+b) ≤ y-log y+2*η := by dsimp [y] at *; linarith
    have hh := mul_le_mul_of_nonneg_left hb hx.le
    dsimp [η] at hslack hh
    nlinarith only [hceil,hslack,hh,mul_nonneg hx.le hε.le]

theorem invert_ceiling (ε : ℝ) (hε : 0<ε) :
    ∃ X Y : ℝ, ∀ x T : ℝ, X≤x → Y≤log T → 0<T → T ≤ (x+17)*log (x+4) →
      T ≤ x*(log T-log (log T)+ε) := by
  obtain ⟨X,Y,h⟩ := invert_shifted_ceiling 17 4 ε (by norm_num) (by norm_num) hε
  refine ⟨max X 0,Y,?_⟩
  intro x T hx hy ht hc
  exact h x T ((le_max_left ..).trans hx) hy ht
    (hc.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) ((le_max_right ..).trans hx))))

#print axioms invert_shifted_ceiling
#print axioms invert_ceiling

end Erdos478.SchurSieve
