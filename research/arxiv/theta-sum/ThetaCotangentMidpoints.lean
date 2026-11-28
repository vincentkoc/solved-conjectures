import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Midpoint approximation for a decreasing logarithmic derivative. -/
namespace Arxiv.«2501.03234».ThetaCotangentMidpoints
open Finset Filter Set
open scoped Topology

private lemma midpoint_error (F g : ℝ → ℝ) {L y : ℝ} (hy : 0<y)
    (hF : ContinuousOn F (Icc 0 L)) (hd : ∀ x∈Ioo 0 L, HasDerivAt F (g x) x)
    (ha : AntitoneOn g (Icc 0 L)) (n : ℕ) (hn : 2*n*y≤L) :
    |(2*y)*(∑ k∈range n,g ((2*(k:ℝ)+1)*y))-(F (2*n*y)-F 0)| ≤
      (2*y)*(g 0-g (2*n*y)) := by
  let t (k : ℕ) := 2*(k:ℝ)*y
  let b (k : ℕ) := (2*(k:ℝ)+1)*y
  have hrow (k : ℕ) (hk : k∈range n) :
      |2*y*g (b k)-(F (t (k+1))-F (t k))|≤2*y*(g (t k)-g (t (k+1))) := by
    have hkn : (k:ℝ)+1≤n := by exact_mod_cast (mem_range.mp hk)
    have h0 : 0≤t k := by dsimp [t]; positivity
    have hl : t (k+1)≤L := by dsimp [t]; push_cast; nlinarith only [hn,mul_le_mul_of_nonneg_right hkn hy.le]
    have hkb : t k<b k := by dsimp [t,b]; linarith
    have hbk : b k<t (k+1) := by dsimp [t,b]; push_cast; linarith
    have hstep : t (k+1)-t k=2*y := by dsimp [t]; push_cast; ring
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope F g (hkb.trans hbk)
      (hF.mono (Icc_subset_Icc h0 hl)) (fun x hx => hd x ⟨h0.trans_lt hx.1,hx.2.trans_le hl⟩)
    rw [hstep,eq_div_iff (by positivity)] at he
    have hleft : t k∈Icc 0 L := ⟨h0,(hkb.trans hbk).le.trans hl⟩
    have hright : t (k+1)∈Icc 0 L := ⟨h0.trans (hkb.trans hbk).le,hl⟩
    have hc' : c∈Icc 0 L := ⟨h0.trans hc.1.le,hc.2.le.trans hl⟩
    have hb' : b k∈Icc 0 L := ⟨h0.trans hkb.le,hbk.le.trans hl⟩
    rw [abs_le]; constructor
    · nlinarith only [he,mul_le_mul_of_nonneg_left (ha hleft hc' hc.1.le) hy.le,
        mul_le_mul_of_nonneg_left (ha hb' hright hbk.le) hy.le]
    · nlinarith only [he,mul_le_mul_of_nonneg_left (ha hleft hb' hkb.le) hy.le,
        mul_le_mul_of_nonneg_left (ha hc' hright hc.2.le) hy.le]
  have H := (abs_sum_le_sum_abs (fun k => 2*y*g (b k)-(F (t (k+1))-F (t k))) (range n)).trans (sum_le_sum hrow)
  rw [sum_sub_distrib,← mul_sum,← mul_sum,sum_range_sub (fun i => F (t i)),sum_range_sub' (fun i => g (t i))] at H
  simpa [t,b] using H
private noncomputable def wave (x : ℝ) := Real.cos x / Real.sin x-x⁻¹
private noncomputable def primitive (x : ℝ) := Real.log (Real.sinc x)

private lemma primitive_deriv {x : ℝ} (hx : x∈Set.Ioo 0 Real.pi) : HasDerivAt primitive (wave x) x := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have h := ((Real.hasDerivAt_sin x).log hsin.ne').sub (Real.hasDerivAt_log hx.1.ne')
  have hl : primitive =ᶠ[nhds x] (fun t => Real.log (Real.sin t)-Real.log t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    simp [primitive,Real.sinc_of_ne_zero ht.1.ne',Real.log_div (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne' ht.1.ne']
  exact h.congr_of_eventuallyEq hl

private lemma wave_deriv {x : ℝ} (hx : x∈Set.Ioo 0 Real.pi) :
    HasDerivAt wave (1/x^2-1/(Real.sin x)^2) x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have h := ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hs.ne').sub (hasDerivAt_inv hx.1.ne')
  have he : -Real.sin x*Real.sin x-Real.cos x*Real.cos x= -1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  rw [he] at h
  exact (show (-1)/(Real.sin x)^2- -(x^2)⁻¹=1/x^2-1/(Real.sin x)^2 by ring) ▸ h

private lemma wave_nonpos_slope {x : ℝ} (hx : x∈Set.Ioo 0 Real.pi) :
    deriv wave x ≤ 0 := by
  rw [(wave_deriv hx).deriv,sub_nonpos]
  exact one_div_le_one_div_of_le (by positivity [Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2])
    (pow_le_pow_left₀ (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).le (Real.sin_le hx.1.le) 2)
private lemma wave_decreases : AntitoneOn wave (Set.Icc 0 (3*Real.pi/4)) := by
  have hp := Real.pi_pos
  have ha : AntitoneOn wave (Set.Ioo 0 Real.pi) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo ..)
    · exact fun x hx => (wave_deriv hx).continuousAt.continuousWithinAt
    · exact fun x hx => (wave_deriv (interior_subset hx)).differentiableAt.differentiableWithinAt
    · exact fun x hx => wave_nonpos_slope (interior_subset hx)
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with he|hx'
  · subst x
    rcases eq_or_lt_of_le hy.1 with he|hy'
    · subst y; exact le_rfl
    · let z := min y (Real.pi/4)
      have hz : 0<z := lt_min hy' (by positivity)
      have hsmall : z<Real.pi/2 := (min_le_right ..).trans_lt (by linarith)
      have htan := inv_anti₀ hz (Real.le_tan hz.le hsmall)
      rw [Real.tan_eq_sin_div_cos,inv_div] at htan
      have hs : wave z≤0 := sub_nonpos.mpr htan
      have hzy : wave y≤wave z := ha ⟨hz,by linarith⟩ ⟨hy',by linarith [hy.2]⟩ (min_le_left ..)
      simpa [wave] using hzy.trans hs
  · exact ha ⟨hx',by linarith [hx.2]⟩ ⟨hx'.trans_le hxy,by linarith [hy.2]⟩ hxy

private lemma continuous_primitive : ContinuousOn primitive (Set.Icc 0 (3*Real.pi/4)) := by
  apply Real.continuous_sinc.continuousOn.log
  intro x hx
  rcases eq_or_lt_of_le hx.1 with he|hpos
  · subst x; simp
  · rw [Real.sinc_of_ne_zero hpos.ne']
    exact (div_pos (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [hx.2,Real.pi_pos])) hpos).ne'
/-- The cotangent error at odd mesh points has an explicit integral limit
when the right endpoint tends to π/2. -/
theorem odd_mesh_correction {y : ℕ → ℝ} {m : ℕ → ℕ}
    (hpos : ∀ᶠ p in atTop, 0<y p) (hy : Tendsto y atTop (𝓝 0))
    (he : Tendsto (fun p => 2*(m p:ℝ)*y p) atTop (𝓝 (Real.pi/2))) :
    Tendsto (fun p => 2*y p*∑ k∈range (m p),
      (Real.cos ((2*(k:ℝ)+1)*y p)/Real.sin ((2*(k:ℝ)+1)*y p)-((2*(k:ℝ)+1)*y p)⁻¹))
      atTop (𝓝 (Real.log (2/Real.pi))) := by
  let L := 3*Real.pi/4
  have hL : Real.pi/2<L := by dsimp [L]; linarith [Real.pi_pos]
  have hu := he.eventually_lt_const hL
  have hzero : primitive 0=0 := by simp [primitive]
  have hp : primitive (Real.pi/2)=Real.log (2/Real.pi) := by
    simp [primitive,Real.sinc_of_ne_zero (by positivity : Real.pi/2≠0),div_div_eq_mul_div]
  have hc : ContinuousAt primitive (Real.pi/2) := Real.continuous_sinc.continuousAt.log
    (by rw [Real.sinc_of_ne_zero (by positivity),Real.sin_pi_div_two]; positivity)
  have hlim := hc.tendsto.comp he
  rw [hp] at hlim
  have hz := ((hy.const_mul 2).mul_const (wave 0-wave L))
  simp only [mul_zero,zero_mul] at hz
  let W (p : ℕ) := 2*y p*∑ k∈range (m p),wave ((2*(k:ℝ)+1)*y p)
  have herr : Tendsto (fun p => W p-primitive (2*(m p:ℝ)*y p)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hz
    filter_upwards [hpos,hu] with p hp' hle
    have H := midpoint_error primitive wave hp' continuous_primitive
      (fun x hx => primitive_deriv (show x∈Set.Ioo 0 Real.pi from ⟨hx.1,by linarith [hx.2,Real.pi_pos]⟩))
      wave_decreases (m p) hle.le
    rw [hzero,sub_zero] at H
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sub_le_sub_left (wave_decreases ⟨by positivity,hle.le⟩ ⟨by positivity,le_rfl⟩ hle.le) _
  simpa only [Function.comp_def,Pi.add_apply,sub_add_cancel,zero_add,W,wave] using herr.add hlim
end Arxiv.«2501.03234».ThetaCotangentMidpoints
#print axioms Arxiv.«2501.03234».ThetaCotangentMidpoints.odd_mesh_correction
