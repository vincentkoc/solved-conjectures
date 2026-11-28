import ThetaUniformExcursionEndpoint

/-! Lower excursions of square-log-log size in the original signed theta sum. -/
namespace Arxiv.«2501.03234».ThetaSquareLogPrimeExcursions
open Finset Filter Real ThetaUniformExcursionEndpoint ThetaUniformExcursions
noncomputable section

theorem integer_scale {a : ℝ} (ha : 0<a) (ha' : a<1/3) (K : ℝ) :
    ∀ᶠ X : ℕ in atTop,
    let L := log (X:ℝ)
    let T := ⌈L^a⌉₊
    1≤L ∧ log L ≤ T ∧ 2147483648*(T:ℝ) ≤ L^(1/3:ℝ) ∧
      (T:ℝ) ≤ 2*L^a ∧ a*log L ≤ log T ∧ K ≤ T := by
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht := (tendsto_rpow_atTop ha).comp hl
  have hh := hl.eventually ((isLittleO_log_rpow_atTop ha).bound zero_lt_one)
  filter_upwards [hl.eventually_ge_atTop 1,ht.eventually_ge_atTop K,hh,
    ((tendsto_rpow_atTop (show 0<1/3-a by linarith)).comp hl).eventually_ge_atTop 4294967296] with X hL hT hlog hgap L T
  change 1≤L at hL
  change K≤L^a at hT
  change 4294967296 ≤ L^(1/3-a:ℝ) at hgap
  have hp : 0<L := by linarith
  have hbig : 1≤L^a := one_le_rpow hL ha.le
  have hlo : L^a ≤ T := Nat.le_ceil _
  have hhi : (T:ℝ) ≤ 2*L^a := by
    have hh := Nat.ceil_lt_add_one (rpow_nonneg hp.le a);change (T:ℝ)<L^a+1 at hh;linarith only [hh,hbig]
  have h₁ : log L ≤ L^a := by
    change ‖log L‖≤1*‖L^a‖ at hlog
    simpa only [Real.norm_of_nonneg (log_nonneg hL),Real.norm_of_nonneg (rpow_nonneg hp.le a),one_mul] using hlog
  have h₂ := mul_le_mul_of_nonneg_left hgap (rpow_nonneg hp.le a)
  rw [←rpow_add hp,show a+(1/3-a)=1/3 by ring] at h₂
  have hg := log_le_log (rpow_pos_of_pos hp a) hlo
  rw [log_rpow hp] at hg
  exact ⟨hL,h₁.trans hlo,by linarith only [hhi,h₂],hhi,hg,hT.trans hlo⟩

/-- Both signs occur above a fixed multiple of (log log X)^2, in every
admitted class, with a lower count uniform in the endpoint and class. -/
theorem original (H : ThetaExceptionalPrimeInput.Ordinary) : ∃ η : ℝ,0<η ∧ ∀ a : ℝ,0<a → a<1/3 →
    ∀ᶠ X : ℕ in atTop,∀ q r : ℕ,0<q → r<q → r.Coprime q → log q ≤ η*(a*log (log X)) →
    ∀ z : ℝ,|z|=1 →
      (X.primeCounting:ℝ)*exp (-(524288*(log (X:ℝ))^a)) ≤
        ((primes X q r z ((a*log (log X))^2/(64*π^2))).card:ℝ) := by
  obtain ⟨η,hη,X₀,he⟩ := endpoints H
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp he
  refine ⟨η,hη,fun a ha ha' => ?_⟩
  filter_upwards [integer_scale ha ha' (T₀:ℝ),eventually_ge_atTop X₀] with X hh hX q r hq hr hcop hqr z hz
  let L := log (X:ℝ)
  let T := ⌈L^a⌉₊
  obtain ⟨hL,hlo,hfit,hhi,hheight,hT₀⟩ := hh
  have ht : T₀≤T := by exact_mod_cast hT₀
  have hqT := hqr.trans (mul_le_mul_of_nonneg_left hheight hη.le)
  have hc := hT T ht X hX hfit q r hq hr hcop hqT z hz
  have hsub : primes X q r z (height T) ⊆ primes X q r z ((a*log L)^2/(64*π^2)) := by
    intro p hp;obtain ⟨hb,hres,he⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨hb,hres,le_trans ?_ he⟩
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg ha.le (log_nonneg hL)) hheight 2) (by positivity)
  apply le_trans _ (hc.trans (Nat.cast_le.mpr (card_le_card hsub)))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply exp_le_exp.mpr
  change (T:ℝ) ≤ 2*L^a at hhi
  linarith only [hhi]

#print axioms original
end
end Arxiv.«2501.03234».ThetaSquareLogPrimeExcursions
