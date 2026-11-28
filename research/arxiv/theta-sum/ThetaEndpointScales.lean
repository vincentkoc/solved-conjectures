import ThetaPrimeBandCalibration

/-! Dyadic index and prime-normalization estimates at arbitrary endpoints. -/
namespace Arxiv.«2501.03234».ThetaEndpointScales
open Filter Real ThetaDenominatorBandScales ThetaPrimeBandCalibration
open scoped Topology
noncomputable section

def index (N : ℕ) := Nat.log 2 ⌊log (N:ℝ)⌋₊

theorem index_tendsto : Tendsto index atTop atTop := by
  refine tendsto_atTop.mpr (fun H => ?_)
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop ((2^H:ℕ):ℝ)] with N hh
  exact Nat.le_log_of_pow_le (by decide : 1<2) ((Nat.le_floor_iff (ThetaDivisorLogMean.log_nonneg_nat N)).mpr hh)

theorem bracket {N : ℕ} (hN : 1 ≤ log (N:ℝ)) :
    (scale (index N):ℝ) ≤ log N ∧ log N ≤ 2*(scale (index N):ℝ) := by
  let M := ⌊log (N:ℝ)⌋₊
  have h₁ : 1 ≤ M := (Nat.le_floor_iff (ThetaDivisorLogMean.log_nonneg_nat N)).mpr (by simpa using hN)
  have hlo := Nat.pow_log_le_self 2 (show M≠0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1<2) M
  rw [pow_succ] at hhi
  have hle : M+1 ≤ 2^Nat.log 2 M*2 := hhi
  constructor
  · exact (show (scale (index N):ℝ) ≤ (M:ℝ) by exact_mod_cast hlo).trans (Nat.floor_le (ThetaDivisorLogMean.log_nonneg_nat N))
  · have h : (M:ℝ)+1 ≤ (scale (index N):ℝ)*2 := by exact_mod_cast hle
    linarith only [h,Nat.lt_floor_add_one (log (N:ℝ))]

theorem absorb {K : ℝ} (_hK : 0 < K) : ∀ᶠ h : ℕ in atTop,
    K*((h:ℝ)+2)*(scale h:ℝ) ≤ exp (saving h/2) := by
  have ht := tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [grows 8 (by norm_num),ht.eventually_ge_atTop K,eventually_ge_atTop 1] with h hh he h₁
  have hr : (1:ℝ) ≤ h := by exact_mod_cast h₁
  have hw : (h:ℝ)+2 ≤ exp (2*(h:ℝ)) := by linarith only [add_one_le_exp (2*(h:ℝ)),hr]
  calc _ ≤ exp (h:ℝ)*exp (2*(h:ℝ))*exp (h:ℝ) :=
         mul_le_mul (mul_le_mul he hw (by positivity) (exp_pos _).le) (bound_scale h).2 (bound_scale h).1.le (by positivity)
       _ ≤ _ := by rw [←exp_add,←exp_add,exp_le_exp];linarith only [hh,hr]

theorem compare {h : ℕ} {x : ℝ} (hlo : (scale h:ℝ) ≤ log x) (hhi : log x ≤ 128*(scale h:ℝ)) :
    rate x/33554432 ≤ saving h/2 := by
  obtain ⟨hw,hh⟩ := width_bound hlo
  have he : rate x ≤ (128*(scale h:ℝ))/(((h:ℝ)+1)/2) := by
    apply div_le_div₀ (by positivity) hhi (by positivity)
    linarith only [hh]
  have hid : (128*(scale h:ℝ))/(((h:ℝ)+1)/2) = 16777216*saving h := by
    unfold saving;push_cast;field_simp;ring
  linarith only [he,hid]

#print axioms compare
end
end Arxiv.«2501.03234».ThetaEndpointScales
