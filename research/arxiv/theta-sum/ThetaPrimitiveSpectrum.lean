import ThetaConductorMultiples
import ThetaSexticNine
import ThetaPrimitiveParity

/-! The full nonprincipal primitive spectrum of the centered prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaPrimitiveSpectrum
open Finset Filter Topology Complex DirichletCharacter ThetaDirichletRows ThetaDirichletMeans
open ThetaDirichletEuler ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPeriodMeans ThetaConditionalRows
open ThetaSexticNine

/-- The character coefficient of the centered prime theta sum. -/
noncomputable def coefficient {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  initial χ (parityFactor χ⁻¹*LFunction χ 1)*∑' n,weight χ n

private lemma projected_limit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ho : Odd q) (hq : 1<q) (hAP : ProgressionMangoldt) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z : ℂ, |L z|≤‖z‖) :
    Tendsto (primeMean (fun n => L (symbol χ n)*residual n)) atTop (𝓝 (L (coefficient χ))) := by
  let A := parityFactor χ⁻¹*LFunction χ 1
  have hne : χ≠1 := by
    intro h
    have H : χ.conductor=q := hχ
    rw [h,conductor_one] at H
    omega
  have hh := (ThetaCharacterHarmonicLimit.harmonic_limit χ hne).1
  have hD : Tendsto (ThetaCharacterSeven.siftedSum (term χ) ∅) atTop (𝓝 (LFunction χ 1)) := by
    apply (hh.comp (tendsto_add_atTop_nat 1)).congr'
    filter_upwards with K
    simp [ThetaCharacterSeven.siftedSum,ThetaCharacterSeven.sift,term,symbol]
  have hmod : OnMod q (fun n => L (symbol χ n)) := fun n => congrArg L (by simp [symbol,ZMod.natCast_mod])
  have hz : unitMean q (fun n => L (symbol χ n))=0 := by
    have hm : ¬χ.conductor∣1 := by rw [show χ.conductor=q from hχ]; exact Nat.not_dvd_of_pos_of_lt (by decide) hq
    simpa using projected_missing χ (dvd_refl q) (one_dvd q) hm L (f:=fun _ => 1) (fun _ => rfl)
  obtain ⟨C,hC,hord⟩ := ThetaPrimeSpectrum.mean_from_rows hAP _ (fun n => (hL _).trans (χ.norm_le_one _)) hmod hz
    1 (fun d => L (rowCoeff χ A d)) (fun hP hd => by simpa only [one_mul,A] using row_projection χ hχ hq hP hd L hD)
  have hs := L.hasSum (coeff_hasSum χ ho A)
  have hseq := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hmatch : Tendsto (fun T => 1*∑ d∈Icc 2 T,L (rowCoeff χ A d)) atTop (𝓝 (L (coefficient χ))) := by
    apply hseq.congr'
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [one_mul,show Icc 2 T=Ico 2 (T+1) by ext i; simp,sum_Ico_eq_sub _ (by omega : 2≤T+1)]
    simp [sum_range_succ,rowCoeff,Nat.not_dvd_of_pos_of_lt (by decide : 0<1) hq]
  rwa [tendsto_nhds_unique hord hmatch] at hC

/-- Complex mean with the same prime set and normalization as the original prime mean. -/
noncomputable def primeMeanC (f : ℕ → ℂ) (X : ℕ) : ℂ := (∑ p∈Nat.primesLE X,f p)/(X.primeCounting:ℂ)

lemma complex_limit {f : ℕ → ℂ} {C : ℂ}
    (hr : Tendsto (fun n => (f n).re) atTop (𝓝 C.re))
    (hi : Tendsto (fun n => (f n).im) atTop (𝓝 C.im)) : Tendsto f atTop (𝓝 C) := by
  have H := ((continuous_ofReal.continuousAt.tendsto.comp hr).add
    ((continuous_ofReal.continuousAt.tendsto.comp hi).mul_const I))
  simpa only [Function.comp_def,re_add_im] using H

lemma components {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ → ℝ) (X : ℕ) :
    (primeMeanC (fun n => symbol χ n*(f n:ℂ)) X).re=primeMean (fun n => (symbol χ n).re*f n) X ∧
    (primeMeanC (fun n => symbol χ n*(f n:ℂ)) X).im=primeMean (fun n => (symbol χ n).im*f n) X := by
  simp [primeMeanC,primeMean,mul_re,mul_im,mul_comm]

/-- All primitive characters of odd conductor greater than one have an explicitly
factorized limiting correlation with the original residual. -/
theorem prime_correlation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ho : Odd q) (hq : 1<q) (hAP : ProgressionMangoldt) :
    Tendsto (primeMeanC (fun p => symbol χ p*((S p:ℝ)/p-Real.log p/2:ℝ))) atTop (𝓝 (coefficient χ)) := by
  apply complex_limit
  · simpa only [ThetaCharacterPrimeMeans.residual, (components χ _ _).1,reCLM_apply] using projected_limit χ hχ ho hq hAP reCLM abs_re_le_norm
  · simpa only [ThetaCharacterPrimeMeans.residual, (components χ _ _).2,imCLM_apply] using projected_limit χ hχ ho hq hAP imCLM abs_im_le_norm

theorem blind_limit {q m : ℕ} [NeZero q] [NeZero m] (χ : DirichletCharacter ℂ q)
    (hm : ¬χ.conductor∣m) (hAP : ProgressionMangoldt) {g : ℕ → ℝ} (hg : OnMod m g) :
    Tendsto (primeMeanC (fun n => symbol χ n*(g n:ℂ))) atTop (𝓝 0) := by
  let P := q*m
  have hq : q∣P := Nat.dvd_mul_right q m
  have hd : m∣P := Nat.dvd_mul_left m q
  have hc (L : ℂ →L[ℝ] ℝ) : Tendsto (primeMean (fun n => L (symbol χ n)*g n)) atTop (𝓝 0) := by
    rw [←projected_missing χ hq hd hm L hg]
    apply periodic_prime_mean hAP
    intro n
    exact congrArg₂ (·*·)
      (congrArg L (onMod_lift hq (f:=symbol χ) (fun j => by simp [symbol,ZMod.natCast_mod]) n))
      (onMod_lift hd hg n)
  apply complex_limit
  · simpa only [(components χ _ _).1,zero_re,reCLM_apply] using hc reCLM
  · simpa only [(components χ _ _).2,zero_im,imCLM_apply] using hc imCLM

/-- A model missing the conductor cannot improve on the magnitude of its Fourier
coefficient in prime mean absolute error. -/
theorem model_obstruction {q m : ℕ} [NeZero q] [NeZero m] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (ho : Odd q) (hq : 1<q) (hm : ¬q∣m) (hAP : ProgressionMangoldt)
    {g : ℕ → ℝ} (hg : OnMod m g) {c : ℝ} (hc : c<‖coefficient χ‖) :
    ∀ᶠ X in atTop,c<primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g p|) X := by
  let f (p : ℕ) := ThetaCharacterPrimeMeans.residual p
  change ∀ᶠ X in atTop,c<primeMean (fun p => |f p-g p|) X
  have H := (prime_correlation χ hχ ho hq hAP).sub (blind_limit χ (by rwa [show χ.conductor=q from hχ]) hAP hg)
  rw [sub_zero] at H
  filter_upwards [H.norm (eventually_gt_nhds hc)] with X hX
  apply hX.trans_le
  have he : primeMeanC (fun p => symbol χ p*(f p:ℂ)) X-primeMeanC (fun p => symbol χ p*(g p:ℂ)) X=
      primeMeanC (fun p => symbol χ p*((f p-g p:ℝ):ℂ)) X := by
    simp only [primeMeanC,ofReal_sub,mul_sub,sum_sub_distrib,sub_div]
  change ‖primeMeanC (fun p => symbol χ p*(f p:ℂ)) X-primeMeanC (fun p => symbol χ p*(g p:ℂ)) X‖≤_
  rw [he,primeMeanC,norm_div,norm_natCast,primeMean]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro p _
  rw [norm_mul,norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)

/-- The observed second ternary digit has a coefficient of magnitude greater than 1/32. -/
theorem nine_bound : 1/32<‖coefficient chi‖ := by
  have hφ : Nat.totient 9=6 := by decide
  have hP : ‖parityFactor chi⁻¹‖=4 := parity_norm
  have hD : (1:ℝ)/2<‖LFunction chi 1‖ := harmonic_real_lower.trans_le (re_le_norm _)
  have hI : ‖1-symbol chi 2/2‖=Real.sqrt 3/2 := two_norm
  have hW := weight_sum_norm chi
  rw [coefficient,initial,norm_mul,norm_div,norm_mul,norm_mul,hP,hI,norm_mul,norm_natCast,norm_natCast,hφ]
  have hs : (27:ℝ)/16<Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  calc _ < 4*‖LFunction chi 1‖*(Real.sqrt 3/2)/(9*6) := by
         nlinarith [mul_pos (sub_pos.mpr hD) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))]
       _ ≤ _ := le_mul_of_one_le_right (by positivity) hW

/-- Every model of period not divisible by nine misses a fixed amount of the
centered original sum, uniformly over these periods. -/
theorem nine_obstruction (hAP : ProgressionMangoldt) {m : ℕ} [NeZero m] (hm : ¬9∣m)
    {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X in atTop,1/32<primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g p|) X :=
  model_obstruction chi chi_primitive (by decide) (by decide) hm hAP hg nine_bound


private theorem even_conductor_projection {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (ho : ¬Odd q) (hq : 1<q) (hAP : ProgressionMangoldt)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ z : ℂ,|L z|≤‖z‖) :
    Tendsto (primeMean (fun n => L (symbol χ n)*ThetaCharacterPrimeMeans.residual n)) atTop (𝓝 0) := by
  have hmod : OnMod q (fun n => L (symbol χ n)) := fun n => congrArg L (by simp [symbol,ZMod.natCast_mod])
  have hz : unitMean q (fun n => L (symbol χ n))=0 := by
    have hm : ¬χ.conductor∣1 := by rw [show χ.conductor=q from hχ]; exact Nat.not_dvd_of_pos_of_lt (by decide) hq
    simpa using projected_missing χ (dvd_refl q) (one_dvd q) hm L (f:=fun _ => 1) (fun _ => rfl)
  have hrows {P d : ℕ} [NeZero P] [NeZero d] (hqp : q∣P) (hd : d∣P) (K : ℕ) :
      unitMean P (fun n => L (symbol χ n)*ThetaRowCorrelations.row d K n)=0 := by
    by_cases hdo : Odd d
    · exact projected_missing χ hqp hd (fun hh => ho (hdo.of_dvd_nat ((show χ.conductor=q from hχ) ▸ hh))) L
        (ThetaRowCorrelations.row_onMod d K)
    · simp [ThetaConditionalRows.even_row hdo,unitMean]
  obtain ⟨C,hC,hord⟩ := ThetaPrimeSpectrum.mean_from_rows hAP _ (fun n => (hL _).trans (χ.norm_le_one _)) hmod hz
    0 (fun _ => 0) (fun hP hd => by simpa only [hrows hP hd,zero_div,zero_mul] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=atTop (α:=ℕ))))
  simp only [zero_mul] at hord
  rwa [tendsto_nhds_unique hord tendsto_const_nhds] at hC

/-- Full nonprincipal primitive spectrum. The centered original prime sum has a nonzero
coefficient exactly when both the conductor and the character are odd. -/
theorem spectrum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1<q) (hAP : ProgressionMangoldt) :
    Tendsto (primeMeanC (fun p => symbol χ p*((S p:ℝ)/p-Real.log p/2:ℝ))) atTop
        (𝓝 (if _root_.Odd q then coefficient χ else 0)) ∧
    ((if _root_.Odd q then coefficient χ else 0)≠0 ↔ _root_.Odd q ∧ χ.Odd) := by
  by_cases ho : _root_.Odd q
  · rw [if_pos ho]
    simp only [ho,true_and]
    refine ⟨prime_correlation χ hχ ho hq hAP,?_⟩
    have hi : (χ⁻¹).IsPrimitive := (conductor_inv χ).trans hχ
    have hne : χ≠1 := by
      intro h
      have H : χ.conductor=q := hχ
      rw [h,conductor_one] at H; omega
    have hW : (∑' n,weight χ n)≠0 := fun h => by have hh := weight_sum_norm χ; rw [h,norm_zero] at hh; linarith
    have htwo : 1-symbol χ 2/2≠0 := by
      intro h
      have H : symbol χ 2=2 := by linear_combination -2*h
      have hb := χ.norm_le_one (2:ZMod q)
      change ‖symbol χ 2‖≤1 at hb
      norm_num [H] at hb
    constructor
    · intro h
      by_contra hodd
      have he := χ.even_or_odd.resolve_right hodd
      have he' : (χ⁻¹).Even := by
        change χ⁻¹ (-1)=1
        rw [MulChar.inv_apply_eq_inv',he,inv_one]
      exact h (by simp [coefficient,initial,ThetaPrimitiveParity.parity_zero χ⁻¹ hi he' ho hq])
    · intro hodd
      have ho' : (χ⁻¹).Odd := by
        change χ⁻¹ (-1)= -1
        rw [MulChar.inv_apply_eq_inv',hodd]; norm_num
      apply mul_ne_zero _ hW
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (ThetaPrimitiveParity.parity_nonzero χ⁻¹ hi ho' ho hq)
        (LFunction_apply_one_ne_zero hne)) htwo) (mul_ne_zero (by exact_mod_cast NeZero.ne q)
          (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'))
  · rw [if_neg ho]
    refine ⟨?_,⟨fun h => (h rfl).elim,fun h => (ho h.1).elim⟩⟩
    apply complex_limit
    · simpa only [(components χ _ _).1,zero_re,reCLM_apply,ThetaCharacterPrimeMeans.residual] using
        even_conductor_projection χ hχ ho hq hAP reCLM abs_re_le_norm
    · simpa only [(components χ _ _).2,zero_im,imCLM_apply,ThetaCharacterPrimeMeans.residual] using
        even_conductor_projection χ hχ ho hq hAP imCLM abs_im_le_norm

/-- Exact nonzero value on the odd primitive spectrum, with all local factors. -/
theorem odd_closed_form {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hodd : χ.Odd) (ho : _root_.Odd q) (hq : 1<q) :
    coefficient χ =
      I*(4*χ⁻¹ 2-2)*gaussSum χ⁻¹ ZMod.stdAddChar*(LFunction χ 1)^2*(1-χ 2/2)/
        ((Real.pi:ℂ)*q*q.totient)*
        ∏' p : Nat.Primes,(1+factor χ p/(((p:ℕ):ℂ)^2-1)) := by
  have hi : (χ⁻¹).IsPrimitive := (conductor_inv χ).trans hχ
  have hio : (χ⁻¹).Odd := by
    change χ⁻¹ (-1)= -1
    rw [MulChar.inv_apply_eq_inv',hodd]; norm_num
  have hne : χ⁻¹≠1 := by
    intro h
    have H : (χ⁻¹).conductor=q := hi
    rw [h,conductor_one] at H; omega
  have hM := ThetaPrimitiveParity.moment_identity χ⁻¹ hi hio hq
  rw [inv_inv] at hM
  have hD := ThetaPrimitiveParity.doubling χ⁻¹ ho hne
  have hq0 : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have HP : parityFactor χ⁻¹=I*(4*χ⁻¹ 2-2)*gaussSum χ⁻¹ ZMod.stdAddChar*LFunction χ 1/Real.pi := by
    field_simp [hq0] at hM
    rw [eq_div_iff hπ]
    apply mul_right_cancel₀ hq0
    linear_combination (norm := (ring_nf; simp [I_sq])) (Real.pi:ℂ)*hD - I*(4*χ⁻¹ 2-2)*hM
  rw [coefficient,initial,HP,product_value]
  simp only [symbol,Nat.cast_ofNat]
  ring

/-- Squarefree periods all miss the second ternary digit. -/
theorem squarefree_obstruction (hAP : ProgressionMangoldt) {m : ℕ} [NeZero m] (hm : Squarefree m)
    {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X in atTop,1/32<primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g p|) X := by
  apply nine_obstruction hAP _ hg
  intro h
  exact (by decide : ¬IsUnit (3:ℕ)) (hm 3 h)

#print axioms odd_closed_form
#print axioms spectrum
#print axioms squarefree_obstruction

#print axioms blind_limit
#print axioms model_obstruction
#print axioms nine_bound
#print axioms nine_obstruction
#print axioms prime_correlation
end Arxiv.«2501.03234».ThetaPrimitiveSpectrum
