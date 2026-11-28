import ThetaDenominatorBandScales
import ThetaHighWindowProjection

/-! The projection costs at most one on a high band. The first band costs two logarithms. -/
namespace Arxiv.«2501.03234».ThetaBandProjectionBudget
open Filter Real ThetaDenominatorBandScales ThetaHighWindowProjection ThetaSmoothConditionalModel ThetaOrbitProjection
open scoped Topology
noncomputable section

private theorem admissible {h q : ℕ} (hq : first h ≤ q) (ht : q ≤ scale h) :
    2 ≤ expose h q ∧ 1 ≤ log (expose h q:ℝ) := by
  have he := (ints hq ht).1
  have hv : steps h q < 2^(steps h q) := Nat.lt_two_pow_self
  refine ⟨by change 2 ≤ 2^(steps h q);omega,?_⟩
  rw [log_expose];have hr : (2:ℝ) ≤ steps h q := by exact_mod_cast (show 2 ≤ steps h q by omega)
  nlinarith only [mul_le_mul_of_nonneg_left (show 1/2 ≤ log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg (α:=ℝ) (steps h q)),hr]

theorem high : ∀ᶠ h : ℕ in atTop,∀ q Y : ℕ,first h ≤ q → q ≤ scale h → 2 ≤ Y →
    ∀ (W : Window),(∀ d,d ≤ (2^q)^2 → W.width d=0) → ∀ n : ℕ,
    |smooth Y (expose h q) (rowModel Y W) n| ≤ 1 := by
  obtain ⟨B,hB⟩ := exists_nat_gt budget
  filter_upwards [eventually_ge_atTop B] with h hh q Y hq ht hy W hw n
  let U := expose h q
  let Q : ℕ := 2^q
  let s := 1/(16*log U)
  obtain ⟨hU,hl⟩ := admissible hq ht
  change 1 ≤ log (U:ℝ) at hl
  have hl' : 0 < log U := by linarith
  have hs : 0 ≤ s := by dsimp [s];positivity
  have hsup : s ≤ 1/16 := by dsimp [s];gcongr;linarith
  have hprod : s*log U=1/16 := by dsimp [s];field_simp
  have hsmall : s*log U ≤ log (3/2) := by
    rw [hprod];have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2);norm_num at this;linarith
  have he := ordinary hy hU hl (show 0 < Q by dsimp [Q];positivity) hs hsup hsmall W hw n
  apply he.trans
  rw [div_le_one (Real.rpow_pos_of_pos (by dsimp [Q];positivity) _),Real.rpow_def_of_pos (by dsimp [Q];positivity)]
  have hi := (ints hq ht).2.2.1
  have hi' : (steps h q:ℝ)*(1024*((h:ℝ)+1)) ≤ q := by exact_mod_cast hi
  have hlow : 64*((h:ℝ)+1) ≤ log Q*s := by
    rw [show log (Q:ℝ)=(q:ℝ)*log 2 by simp [Q,log_pow]]
    dsimp only [s];rw [mul_one_div,le_div_iff₀ (by positivity)]
    rw [show log (U:ℝ)=_ from log_expose h q]
    nlinarith only [mul_le_mul_of_nonneg_right hi' (show 0 ≤ log 2 by linarith [log_two_gt_d9])]
  have hbudget : budget ≤ exp (h:ℝ) := hB.le.trans ((Nat.cast_le.mpr hh).trans (le_trans (by linarith : (h:ℝ) ≤ h+1) (Real.add_one_le_exp _)))
  have hup : log U ≤ exp (h:ℝ) := by
    rw [show log (U:ℝ)=_ from log_expose h q]
    have hd : steps h q ≤ q := Nat.div_le_self ..
    apply (mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith [log_two_lt_d9])).trans
    apply (Nat.cast_le.mpr (hd.trans ht)).trans
    rw [←Real.log_le_log_iff (by dsimp [scale];positivity) (exp_pos _),log_scale,log_exp]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith [log_two_lt_d9])
  apply (mul_le_mul hbudget (pow_le_pow_left₀ hl'.le hup 2) (sq_nonneg _) (exp_pos _).le).trans
  rw [←exp_nat_mul,←exp_add,exp_le_exp];push_cast;linarith only [hlow,Nat.cast_nonneg (α:=ℝ) h]

theorem low {h : ℕ} (hh : first h ≤ scale h) {Y : ℕ} (hY : 2 ≤ Y) (W : Window) (n : ℕ) :
    |smooth Y (expose h (first h)) (rowModel Y W) n| ≤ envelope*238*(64*((h:ℝ)+1))^2 := by
  obtain ⟨hu,hl⟩ := admissible (q:=first h) le_rfl hh
  have bound := smooth_baseline hY hu hl W n
  apply bound.trans
  unfold ThetaModelExponentialMoment.height
  have hsteps : steps h (first h)=64*(h+1) := by
    unfold steps first;rw [show 65536*(h+1)^2=64*(h+1)*(1024*(h+1)) by ring,Nat.mul_div_cancel _ (by positivity)]
  have H : log (expose h (first h):ℝ) ≤ 64*((h:ℝ)+1) := by
    rw [log_expose,hsteps];push_cast
    exact mul_le_of_le_one_right (by positivity) (by linarith [log_two_lt_d9])
  have hh' := pow_le_pow_left₀ (zero_le_one.trans hl) H 2
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh' (by norm_num : (0:ℝ) ≤ 238)) envelope_nonneg).trans_eq (by ring)

#print axioms high
end
end Arxiv.«2501.03234».ThetaBandProjectionBudget
