import ThetaSparseCubicEnergy

/-! The real-energy proportion also tends to one half among the large orders. -/

namespace Arxiv.«2501.03234».ThetaHighAngularEnergy
open Filter Finset Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaSparseCubicMass ThetaSignedCubicMass ThetaCubicEnergy ThetaCubicEnergyLimit
noncomputable section

private lemma stable {η T R t r : ℝ} (hη : 0<η) (hT : 0<T) (hr : 0≤r) (hrt : r≤t)
    (ht₁ : t≤T/4) (ht₂ : t≤η*T/4) (h : |R/T-1/2|<η/8) :
    |(R-r)/(T-t)-1/2|<η := by
  have hh : 0<T-t := by linarith
  rw [show R/T-1/2=(R-T/2)/T by field_simp,abs_div,abs_of_pos hT,
    div_lt_iff₀ hT,abs_lt] at h
  rw [show (R-r)/(T-t)-1/2=(R-r-(T-t)/2)/(T-t) by field_simp,
    abs_div,abs_of_pos hh,div_lt_iff₀ hh,abs_lt]
  have hmul := mul_le_mul_of_nonneg_left ht₁ hη.le
  constructor <;> nlinarith only [h.1,h.2,hr,hrt,ht₂,hmul,mul_pos hη hT]

theorem high_fraction {ε η : ℝ} (he : 0<ε) (hη : 0<η) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      |realEnergy (large p ε)/total (large p ε)-1/2|<η := by
  let b := min (1:ℝ) η/4096
  have hb : 0<b := by dsimp [b]; positivity
  filter_upwards [ThetaSparseCubicEnergy.negligible he hb, half_fraction (show 0<η/8 by positivity)]
    with p hl hall
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  let T := total (nonprincipal p)
  let R := realEnergy (nonprincipal p)
  let t := total (low p ε)
  let r := realEnergy (low p ε)
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hh := lower (Nat.odd_iff.mp ho)
  have hφ : (p:ℝ)≤2*(p.totient:ℝ) := by
    rw [Nat.totient_prime hp]
    exact_mod_cast (show p≤2*(p-1) by have := hp.two_le; omega)
  have hT₀ : (p:ℝ)^4≤1024*T := by
    have h := pow_le_pow_left₀ hx.le hφ 4
    change _≤T at hh
    linarith
  have hT : 0<T := by nlinarith only [hT₀,pow_pos hx 4]
  have hlow : t≤b*(p:ℝ)^4 := hl hp ho
  have h₁ : t≤T/4 := by
    have hh' := mul_le_mul_of_nonneg_left hT₀ hb.le
    have b₁ : 4096*b≤1 := by dsimp [b]; linarith [min_le_left (1:ℝ) η]
    nlinarith only [hlow,hh',mul_le_mul_of_nonneg_right b₁ hT.le]
  have h₂ : t≤η*T/4 := by
    have hh' := mul_le_mul_of_nonneg_left hT₀ hb.le
    have b₂ : 4096*b≤η := by dsimp [b]; linarith [min_le_right (1:ℝ) η]
    nlinarith only [hlow,hh',mul_le_mul_of_nonneg_right b₂ hT.le]
  have hr : 0≤r := sum_nonneg (fun _ _ => sq_nonneg _)
  have hrt : r≤t := by
    have h := energy_add (low p ε)
    have hnon : 0 ≤ imagEnergy (low p ε) := sum_nonneg (fun _ _ => sq_nonneg _)
    change r+_=t at h
    linarith
  have ht := sum_filter_add_sum_filter_not (nonprincipal p) (fun χ => (orderOf χ:ℝ)≤(p:ℝ)^(1-ε))
    (fun χ => ‖cubic χ‖^2)
  have hreal := sum_filter_add_sum_filter_not (nonprincipal p) (fun χ => (orderOf χ:ℝ)≤(p:ℝ)^(1-ε))
    (fun χ => ((cubic χ).re)^2)
  change t+total (large p ε)=T at ht
  change r+realEnergy (large p ε)=R at hreal
  rw [show total (large p ε)=T-t by linarith,show realEnergy (large p ε)=R-r by linarith]
  exact stable hη hT hr hrt h₁ h₂ (hall hp ho)

#print axioms high_fraction
end
end Arxiv.«2501.03234».ThetaHighAngularEnergy
