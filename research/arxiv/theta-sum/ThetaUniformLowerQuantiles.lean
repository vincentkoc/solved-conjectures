import ThetaUniformExcursionEndpoint

/-! Finite lower quantiles, simultaneously in the endpoint, level, sign and residue class. -/
namespace Arxiv.«2501.03234».ThetaUniformLowerQuantiles
open Filter Finset Real ThetaUniformExcursionEndpoint ThetaUniformExcursions
noncomputable section

def scale (k : ℝ) := ⌈(k:ℝ)^(1/8:ℝ)⌉₊

private theorem sizes (K : ℝ) : ∀ᶠ k : ℝ in atTop,
    K ≤ scale k ∧ 1 ≤ log (k:ℝ) ∧ log k/8 ≤ log (scale k) ∧
    (scale k:ℝ) ≤ 2*(k:ℝ)^(1/8:ℝ) ∧ 262144*(scale k:ℝ) ≤ k := by
  have hn : Tendsto (id : ℝ → ℝ) atTop atTop := tendsto_id
  have ha := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp hn
  have hb := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/8)).comp hn
  filter_upwards [hn.eventually_ge_atTop 1,ha.eventually_ge_atTop K,hb.eventually_ge_atTop 524288,
    (tendsto_log_atTop.comp hn).eventually_ge_atTop 1] with k hk hK hgap hlog
  change 1≤(k:ℝ) at hk
  change 524288 ≤ (k:ℝ)^(7/8:ℝ) at hgap
  have hp : 0<(k:ℝ) := by linarith
  have hl : (k:ℝ)^(1/8:ℝ) ≤ scale k := Nat.le_ceil _
  have hu : (scale k:ℝ) ≤ 2*(k:ℝ)^(1/8:ℝ) := by
    have ht := Nat.ceil_lt_add_one (rpow_nonneg hp.le (1/8))
    change (scale k:ℝ)<(k:ℝ)^(1/8:ℝ)+1 at ht
    linarith only [ht,one_le_rpow hk (by norm_num : (0:ℝ)≤1/8)]
  have h := mul_le_mul_of_nonneg_left hgap (rpow_nonneg hp.le (1/8))
  rw [←rpow_add hp,show (1/8+7/8:ℝ)=1 by norm_num,rpow_one] at h
  have hg := log_le_log (rpow_pos_of_pos hp (1/8)) hl
  rw [log_rpow hp] at hg
  exact ⟨le_trans hK hl,hlog,by linarith,hu,by linarith only [hu,h]⟩

private theorem gap : ∀ᶠ X : ℕ in atTop,
    1≤log (X:ℝ) ∧ 4294967296*(log (X:ℝ))^(1/8:ℝ) ≤ (log (X:ℝ))^(1/3:ℝ) := by
  have h := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually_ge_atTop 1,((tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/24)).comp h).eventually_ge_atTop 4294967296] with X hL hg
  change 1≤log (X:ℝ) at hL
  change 4294967296≤(log (X:ℝ))^(5/24:ℝ) at hg
  refine ⟨hL,?_⟩
  have hp : 0<log (X:ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right hg (rpow_nonneg hp.le (1/8))
  rwa [←rpow_add hp,show (5/24+1/8:ℝ)=1/3 by norm_num] at hh

theorem original (H : ThetaExceptionalPrimeInput.Ordinary) :
    ∃ δ : ℝ,0<δ ∧ ∃ t₀ : ℝ,∀ᶠ X : ℕ in atTop,
    ∀ t≥t₀,t ≤ log (X:ℝ) → ∀ q r : ℕ,0<q → r<q → r.Coprime q → log q ≤ δ*log t →
    ∀ z : ℝ,|z|=1 → (X.primeCounting:ℝ)*exp (-t) ≤
      ((primes X q r z ((1+log t)^2/(16384*π^2))).card:ℝ) := by
  obtain ⟨η,hη,X₀,he⟩ := endpoints H
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp he
  obtain ⟨t₀,hsize⟩ := eventually_atTop.mp (sizes T₀)
  refine ⟨η/8,by positivity,t₀,?_⟩
  filter_upwards [gap,eventually_ge_atTop X₀] with X hgap hX t ht hhi q r hq hr hc hqr z hz
  obtain ⟨hT₀,hlog,hheight,hw,hcost⟩ := hsize t ht
  have htpos : 0≤t := by linarith only [hcost,Nat.cast_nonneg (α:=ℝ) (scale t)]
  have hh : 2147483648*(scale t:ℝ) ≤ (log (X:ℝ))^(1/3:ℝ) := by
    have hv := rpow_le_rpow htpos hhi (by norm_num : (0:ℝ)≤1/8)
    linarith only [hw,hv,hgap.2]
  have hmod : log q ≤ η*log (scale t) := by
    linarith only [hqr,mul_le_mul_of_nonneg_left hheight hη.le]
  have hp := hT (scale t) (by exact_mod_cast hT₀) X hX hh q r hq hr hc hmod z hz
  have hv : (1+log t)^2/(16384*π^2) ≤ height (scale t) := by
    have hs := pow_le_pow_left₀ (by linarith : 0≤1+log t)
      (show 1+log t≤16*log (scale t) by linarith only [hlog,hheight]) 2
    unfold height
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg π)]
  have hsub : primes X q r z (height (scale t)) ⊆ primes X q r z ((1+log t)^2/(16384*π^2)) := by
    intro p hp
    obtain ⟨hs,hres,h⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hs,hres,hv.trans h⟩
  exact ((mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)).trans hp).trans
    (Nat.cast_le.mpr (card_le_card hsub))

#print axioms original
end
end Arxiv.«2501.03234».ThetaUniformLowerQuantiles
