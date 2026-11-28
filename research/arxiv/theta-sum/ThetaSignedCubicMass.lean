import ThetaSparseCubicMass

/-! Positive and negative contributions above p^(1−ε) both greatly exceed the signed theta sum. -/
namespace Arxiv.«2501.03234».ThetaSignedCubicMass
open Finset Filter Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaAbsoluteCubicMass ThetaSparseCubicMass
noncomputable section

def large (p : ℕ) [Fact p.Prime] (ε : ℝ) :=
  (nonprincipal p).filter (fun χ => ¬(orderOf χ:ℝ)≤(p:ℝ)^(1-ε))

def positive {p : ℕ} [Fact p.Prime] (D : Finset (DirichletCharacter ℂ p)) :=
  ∑ χ∈D,max (cubic χ).re 0

def negative {p : ℕ} [Fact p.Prime] (D : Finset (DirichletCharacter ℂ p)) :=
  ∑ χ∈D,max (-(cubic χ).re) 0

private lemma split {p : ℕ} [Fact p.Prime] (D : Finset (DirichletCharacter ℂ p)) :
    positive D+negative D=mass D ∧ positive D-negative D=∑ χ∈D,(cubic χ).re := by
  unfold positive negative mass
  rw [←sum_add_distrib,←sum_sub_distrib]
  constructor <;> apply sum_congr rfl <;> intro χ _
  all_goals rcases le_total 0 (cubic χ).re with h|h
  all_goals simp [h,abs_of_nonneg,abs_of_nonpos]

theorem signed_bound {b : ℝ} (hb : 0<b) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      |∑ χ∈nonprincipal p,(cubic χ).re| ≤ b*scale p := by
  have H := (ThetaFourier.S_isLittleO_prime_rpow (by norm_num : (0:ℝ)<1/2)).bound hb
  rw [eventually_inf_principal] at H
  filter_upwards [H] with p h
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  specialize h hp
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx.le (Real.sqrt_nonneg _)),rpow_add hx,rpow_one,←sqrt_eq_rpow] at h
  have hd := congrArg Complex.re (expansion (p:=p) ho)
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,zero_mul,sub_zero,Complex.re_sum] at hd
  norm_num at hd
  change (p.totient:ℝ)*(S p:ℝ)=4*∑ χ∈nonprincipal p,(cubic χ).re at hd
  have ha := congrArg abs hd
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at ha
  have hφ : (p.totient:ℝ)≤p := by exact_mod_cast Nat.totient_le p
  have hu := mul_le_mul hφ h (abs_nonneg _) hx.le
  unfold scale
  nlinarith only [ha,hu,abs_nonneg (∑ χ∈nonprincipal p,(cubic χ).re)]

theorem both_unscaled {ε : ℝ} (he : 0<ε) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      scale p/2048 ≤ positive (large p ε) ∧ scale p/2048 ≤ negative (large p ε) := by
  filter_upwards [eventually_lower,signed_bound (by norm_num : (0:ℝ)<1/8192),
    ThetaSparseCubicMass.negligible he (by norm_num : (0:ℝ)<1/8192)] with p hA hS hL
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  specialize hA hp ho
  specialize hS hp ho
  specialize hL hp ho
  have ha := sum_filter_add_sum_filter_not (nonprincipal p) (fun χ => (orderOf χ:ℝ)≤(p:ℝ)^(1-ε))
    (fun χ => |(cubic χ).re|)
  change mass (low p ε)+mass (large p ε)=mass (nonprincipal p) at ha
  have hs := sum_filter_add_sum_filter_not (nonprincipal p) (fun χ => (orderOf χ:ℝ)≤(p:ℝ)^(1-ε))
    (fun χ => (cubic χ).re)
  change (∑ χ∈low p ε,(cubic χ).re)+(∑ χ∈large p ε,(cubic χ).re)=_ at hs
  have hsmall : |∑ χ∈low p ε,(cubic χ).re| ≤ mass (low p ε) := Finset.abs_sum_le_sum_abs ..
  obtain ⟨hw,hd⟩ := split (large p ε)
  have hp0 : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hscale : 0≤ scale p := by unfold scale; positivity
  have pos : scale p/2048≤ positive (large p ε) := by
    linarith only [hw,hd,ha,hs,(abs_le.mp hS).1,(abs_le.mp hsmall).2,hA,hL,hscale]
  have neg : scale p/2048≤ negative (large p ε) := by
    linarith only [hw,hd,ha,hs,(abs_le.mp hS).2,(abs_le.mp hsmall).1,hA,hL,hscale]
  exact ⟨pos,neg⟩

/-- Each sign contributes at least p√p/512 to S(p) after normalization by 4/(p−1),
even among characters whose order exceeds p^(1−ε). -/
theorem both_signs {ε : ℝ} (he : 0<ε) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (p:ℝ)*Real.sqrt p/512 ≤ 4/(p.totient:ℝ)*positive (large p ε) ∧
      (p:ℝ)*Real.sqrt p/512 ≤ 4/(p.totient:ℝ)*negative (large p ε) := by
  filter_upwards [both_unscaled he] with p H
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨pos,neg⟩ := H hp ho
  have hp0 : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hφ : 0<(p.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hp.pos)
  have hφp : (p.totient:ℝ)≤p := by exact_mod_cast Nat.totient_le p
  have transfer (x : ℝ) (h : scale p/2048≤x) : (p:ℝ)*Real.sqrt p/512≤4/(p.totient:ℝ)*x := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hφ]
    unfold scale at h
    nlinarith only [h,mul_le_mul_of_nonneg_left hφp (mul_nonneg hp0.le (Real.sqrt_nonneg (p:ℝ)))]
  exact ⟨transfer _ pos,transfer _ neg⟩

#print axioms both_signs
#print axioms signed_bound
end
end Arxiv.«2501.03234».ThetaSignedCubicMass
