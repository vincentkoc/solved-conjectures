import ThetaMultiscalePrimeBand

/-! Calibration of the band threshold and the count in original theta variables. -/
namespace Arxiv.«2501.03234».ThetaPrimeBandCalibration
open Filter Real Finset ThetaDenominatorBandScales ThetaMultiscaleRows ThetaSmoothConditionalModel
open scoped Topology
noncomputable section

def width (x : ℝ) := 1+log (log x)
def rate (x : ℝ) := log x/width x

theorem bound_scale (h : ℕ) : 0 < (scale h:ℝ) ∧ (scale h:ℝ) ≤ exp (h:ℝ) := by
  have hp : 0 < (scale h:ℝ) := by dsimp [scale];positivity
  refine ⟨hp,?_⟩
  rw [←log_le_log_iff hp (exp_pos _),log_scale,log_exp]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith [log_two_lt_d9])

theorem saving_le (h : ℕ) : 0 ≤ saving h ∧ saving h ≤ scale h := by
  dsimp [saving]
  constructor
  · positivity
  · apply div_le_self (Nat.cast_nonneg _) _;push_cast;linarith [Nat.cast_nonneg (α:=ℝ) h]

theorem grows (K : ℝ) (hK : 0 < K) : ∀ᶠ h : ℕ in atTop,K*((h:ℝ)+1) ≤ saving h := by
  have hf := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)
  filter_upwards [hf.eventually_le_const (by positivity : (0:ℝ)<1/(262144*K)),eventually_ge_atTop 1] with h hh h₁
  change (h:ℝ)^2/(2:ℝ)^h ≤ _ at hh
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hh
  have hreal : (1:ℝ) ≤ h := by exact_mod_cast h₁
  have htwo : (h:ℝ)+1 ≤ 2*(h:ℝ) := by linarith only [hreal]
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ (h:ℝ)+1) htwo 2) hK.le
  dsimp [saving,scale];push_cast;rw [le_div_iff₀ (by positivity)]
  nlinarith only [hs,hh]

theorem width_bound {h : ℕ} {x : ℝ} (hx : (scale h:ℝ) ≤ log x) :
    1 ≤ width x ∧ (h:ℝ)+1 ≤ 2*width x := by
  have hh := log_le_log (bound_scale h).1 hx
  rw [log_scale] at hh
  have hn := mul_le_mul_of_nonneg_left (show 1/2 ≤ log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg (α:=ℝ) h)
  unfold width;constructor <;> linarith only [hh,hn,Nat.cast_nonneg (α:=ℝ) h]

theorem threshold {C : ℝ} (hC : 0 < C) : ∃ A : ℝ,0 < A ∧ ∀ h : ℕ,∀ x : ℝ,(scale h:ℝ) ≤ log x →
    C+(8/π^2)*(level h+1) ≤ A*(width x)^2 := by
  let V := envelope*238*64^2
  have hV : 0 ≤ V := by dsimp [V];positivity [envelope_nonneg]
  let K := 8/π^2
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨C+K*(8+4*V),by positivity,fun h x hh => ?_⟩
  obtain ⟨h₁,h₂⟩ := width_bound hh
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (h:ℝ)+1) h₂ 2
  have hsq : 1 ≤ (width x)^2 := one_le_pow₀ h₁
  have hx : width x ≤ (width x)^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr h₁) (zero_le_one.trans h₁)]
  have hl : level h+1 ≤ (8+4*V)*(width x)^2 := by
    change (1+envelope*238*(64*((h:ℝ)+1))^2)+2*((h:ℝ)+1)+1 ≤ _
    have h := mul_le_mul_of_nonneg_left hs hV
    dsimp [V] at *;nlinarith only [h,hsq,hx,h₂]
  change C+K*_ ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left hl hK.le,mul_le_mul_of_nonneg_left hsq hC.le]

theorem band : ∃ A D : ℝ,0 < A ∧ 0 < D ∧ ∀ᶠ h : ℕ in atTop,∀ N : ℕ,2 ≤ N → (scale h:ℝ) ≤ log N →
    ∀ V : Finset ℕ,(∀ p∈V,p.Prime ∧ N^56 ≤ p ∧ p ≤ N^64 ∧
      A*(width p)^2 ≤ |(S p:ℝ)/p-log p/2|) →
    (V.card:ℝ) ≤ D*((h:ℝ)+2)*(N:ℝ)^64*exp (-saving h) := by
  obtain ⟨C,B,hC,hB,H⟩ := ThetaMultiscalePrimeBand.raw
  obtain ⟨A,hA,hthr⟩ := threshold hC
  let K := 2*exp ThetaTiltBudget.total
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨A,B+2*K+2,hA,by positivity,?_⟩
  filter_upwards [H] with h hband N hN hl V hV
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have he := hband N hN hl V (by
    intro p hp;obtain ⟨hpr,hlo,hhi,hx⟩ := hV p hp
    have hnp : N ≤ p := (Nat.le_self_pow (by decide : 56≠0) N).trans hlo
    exact ⟨hpr,hlo,hhi,(hthr h p (hl.trans (log_le_log hn (by exact_mod_cast hnp)))).trans hx⟩)
  have hsmall : exp (18*scale h) ≤ (N:ℝ)^64*exp (-saving h) := by
    rw [show (N:ℝ)^64=exp ((64:ℝ)*log N) by rw [show (64:ℝ)=(64:ℕ) by norm_num,exp_nat_mul,exp_log hn],←exp_add,exp_le_exp]
    linarith only [(saving_le h).2,hl,(bound_scale h).1]
  have ht : 1/(size (scale h):ℝ)^(1/64:ℝ) ≤ exp (-saving h) := by
    have hp : 0 < (size (scale h):ℝ) := by dsimp [size];positivity
    rw [Real.rpow_def_of_pos hp,one_div,←Real.exp_neg,log_size,exp_le_exp]
    have hb := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ log 2 by linarith [log_two_gt_d9]) (bound_scale h).1.le
    unfold saving;push_cast;rw [neg_le_neg_iff,div_le_iff₀ (by positivity)]
    have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg _
    nlinarith only [hb,mul_nonneg (mul_nonneg (bound_scale h).1.le (log_pos (by norm_num : (1:ℝ)<2)).le) hh]
  have hp' : 1 ≤ (N:ℝ)^64 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ N by omega))
  have hN₁ : ((N^64+1:ℕ):ℝ) ≤ 2*(N:ℝ)^64 := by push_cast;linarith
  let v := (N:ℝ)^64*exp (-saving h)
  have hv : 0 ≤ v := by dsimp [v];positivity
  have ha : error h (N^64+1) ≤ (2*K+2)*v := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN₁ hK.le) (exp_pos (-saving h)).le
    dsimp only [error,K,v] at *;linarith only [h,hsmall]
  have hb : B*(N:ℝ)^64/(size (scale h):ℝ)^(1/64:ℝ) ≤ B*v := by
    have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg hB (pow_nonneg hn.le 64))
    simpa only [v, div_eq_mul_inv, one_mul, mul_assoc] using hh
  have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ (h:ℝ)+2 by positivity)
  have hx := mul_le_mul_of_nonneg_right (show 1 ≤ (h:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) h]) (mul_nonneg hB hv)
  change _ ≤ _*_*((N:ℝ)^64)*exp (-saving h)
  dsimp only [v] at *;nlinarith only [he,hb,hh,hx]

#print axioms band
end
end Arxiv.«2501.03234».ThetaPrimeBandCalibration
