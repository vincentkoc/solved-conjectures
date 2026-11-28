import ThetaSmoothConditionalModel

/-! Exponential tilts whose total variance charge is bounded uniformly. -/
namespace Arxiv.«2501.03234».ThetaTiltBudget
open Real Filter Finset ThetaSmoothConditionalModel
open scoped Topology
noncomputable section

def tilt (T : ℕ) := (T:ℝ)^(1/4:ℝ)
def size (q : ℕ) := (q:ℝ)^(-(7:ℝ)/8)
def charge (q : ℕ) := (q:ℝ)^(-(5:ℝ)/4)
def total := ∑' q : ℕ,charge q

theorem eventual_size : ∀ᶠ q : ℕ in atTop, 544*envelope*(log q)^2/q ≤ size q := by
  have h : Tendsto (fun q : ℕ => (log q)^2/(q:ℝ)^(1/8:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/8)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have H := (h.const_mul (544*envelope)).eventually_lt_const (by simp : (544*envelope)*0<1)
  filter_upwards [H,eventually_ge_atTop 1] with q hq hpos
  have hx : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hpow := Real.rpow_pos_of_pos hx (1/8:ℝ)
  change 544*envelope*((log q)^2/(q:ℝ)^(1/8:ℝ))<1 at hq
  have hsmall : 544*envelope*(log q)^2≤(q:ℝ)^(1/8:ℝ) := by
    rw [← mul_div_assoc,div_lt_iff₀ hpow,one_mul] at hq
    exact le_of_lt hq
  apply (div_le_iff₀ hx).mpr
  calc
    _ ≤ (q:ℝ)^(1/8:ℝ) := hsmall
    _ = size q*q := by
      unfold size
      conv_rhs => rhs;rw [← Real.rpow_one (q:ℝ)]
      rw [← Real.rpow_add hx];norm_num

theorem tilt_pos {T : ℕ} (h : 0<T) : 0<tilt T := Real.rpow_pos_of_pos (Nat.cast_pos.mpr h) _

theorem within {T q : ℕ} (hT : 1≤T) (hq : T≤q) {v : ℝ} (hv : |v|=tilt T) :
    |v| * size q≤1 ∧ v^2*(size q)^2≤charge q := by
  have hx : (1:ℝ)≤q := by exact_mod_cast hT.trans hq
  have hp : (0:ℝ)<q := by linarith
  have ht : tilt T ≤ (q:ℝ)^(1/4:ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hq) (by norm_num)
  have hab : |v| * size q ≤ (q:ℝ)^(-(5:ℝ)/8) := calc
    _ ≤ (q:ℝ)^(1/4:ℝ)*(q:ℝ)^(-(7:ℝ)/8) := by
      rw [hv]; exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_add hp];norm_num
  constructor
  · exact hab.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num))
  · have H := pow_le_pow_left₀ (mul_nonneg (abs_nonneg v) (Real.rpow_nonneg hp.le _)) hab 2
    rw [mul_pow,sq_abs] at H
    apply H.trans_eq
    unfold charge
    rw [← Real.rpow_two,← Real.rpow_mul hp.le];norm_num

theorem bounded (s : Finset ℕ) : ∑ q∈s,charge q≤total := by
  have hs : Summable charge := Real.summable_nat_rpow.mpr (by norm_num)
  exact hs.sum_le_tsum s (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _)

#print axioms eventual_size
#print axioms within
end
end Arxiv.«2501.03234».ThetaTiltBudget
