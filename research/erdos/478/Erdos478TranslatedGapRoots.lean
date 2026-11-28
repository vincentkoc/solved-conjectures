import Erdos478TranslatedGapPolynomials
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Complex root locations of translated factorial-gap polynomials -/

namespace Erdos478.LocalSpacing
open Polynomial Finset

/-- A root lies within one of a negated integer in the endpoint interval. -/
theorem root_near_centre {r k : ℕ} (hk : 0<k) (hkr : k≤r) {z : ℂ}
    (hz : (translatedGap ℂ r k).IsRoot z) :
    ∃ a : ℕ, a≤r ∧ ‖z+(a:ℂ)‖≤1 := by
  have hp : ∏ i ∈ range k, (z+(r:ℂ)-i)=1 := by
    simpa only [IsRoot.def,translatedGap,taylor_eval,eval_sub,eval_one,sub_eq_zero,
      descPochhammer_eval_eq_prod_range] using hz
  by_contra! h
  have big (i : ℕ) (hi : i∈range k) : 1<‖z+(r:ℂ)-i‖ := by
    have ir := (mem_range.mp hi).le.trans hkr
    simpa only [Nat.cast_sub ir,← add_sub_assoc] using h (r-i) (Nat.sub_le ..)
  have g := prod_lt_prod (s:=range k) (f:=fun _ => (1:ℝ)) (fun _ _ => zero_lt_one)
    (fun i hi => (big i hi).le) ⟨0,mem_range.mpr hk,big 0 (mem_range.mpr hk)⟩
  have hn := congrArg (fun v : ℂ => ‖v‖) hp
  simp only [norm_prod,norm_one] at hn
  simp [hn] at g

theorem root_difference_bound {r s k l H : ℕ} (hk : 0<k) (hl : 0<l)
    (hkr : k≤r) (hls : l≤s) (hr : r≤H) (hs : s≤H) {z w : ℂ}
    (hz : (translatedGap ℂ r k).IsRoot z) (hw : (translatedGap ℂ s l).IsRoot w) :
    ‖z-w‖≤(H:ℝ)+2 := by
  obtain ⟨a,ha,hn⟩ := root_near_centre hk hkr hz
  obtain ⟨b,hb,hm⟩ := root_near_centre hl hls hw
  have c : ‖(b:ℂ)-a‖≤(H:ℝ) := by
    rw [show (b:ℂ)-a=(((b:ℝ)-a:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,Real.norm_eq_abs,abs_le]
    have aa : (a:ℝ)≤H := by exact_mod_cast ha.trans hr
    have bb : (b:ℝ)≤H := by exact_mod_cast hb.trans hs
    constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) a,Nat.cast_nonneg (α:=ℝ) b]
  calc
    ‖z-w‖=‖((z+a)+((b:ℂ)-a))-(w+b)‖ := by congr 1; ring
    _ ≤ ‖(z+a)+((b:ℂ)-a)‖+‖w+b‖ := norm_sub_le ..
    _ ≤ (H:ℝ)+2 := by linarith [norm_add_le (z+(a:ℂ)) ((b:ℂ)-a)]

#print axioms root_near_centre
#print axioms root_difference_bound
end Erdos478.LocalSpacing
