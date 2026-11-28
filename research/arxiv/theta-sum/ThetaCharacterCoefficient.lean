import ThetaCharacterNumerator
import ThetaCharacterEuler
import ThetaPrimeTailTransfer
import ThetaCharacterPrimeMeans

/-! Exact finite-denominator coefficients of the modulo-three prime correlation. -/
namespace Arxiv.«2501.03234».ThetaCharacterCoefficient
open Finset Filter ThetaCharacterThree ThetaPrimeTailTransfer ThetaRowCorrelations
open ThetaReciprocalBlocks ThetaReciprocalInversion ThetaConditionalRows ThetaDivisibleDiagonal
open ThetaPrimeMeanSquare ThetaCharacterEuler ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open ThetaDiagonalConstant
open scoped Topology

local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos n).ne'⟩

private lemma commonWeight_eq (Y d : ℕ) :
    commonWeight Y d = ∑ k ∈ range ((Y/d+1)/2), ((2*(k:ℝ)+1)^2)⁻¹ := by
  symm
  unfold commonWeight
  refine sum_bij' (fun k _ => 2*k+1) (fun g _ => g/2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have := mem_range.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro g hg
    obtain ⟨hg,hodd⟩ := mem_filter.mp hg
    obtain ⟨hl,hh⟩ := mem_Icc.mp hg
    exact mem_range.mpr (by omega)
  · intro k _
    omega
  · intro g hg
    have := (mem_filter.mp hg).2
    omega
  · intro k _
    push_cast
    rfl

private theorem weight_limit {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => commonWeight (2*N^52) d) atTop (𝓝 (Real.pi^2/8)) := by
  simp_rw [commonWeight_eq]
  apply odd_reciprocal_square.tendsto_sum_nat.comp
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (d*(2*b))] with N hN
  have hh := Nat.le_self_pow (by decide : 52≠0) N
  have hb : 2*b ≤ 2*N^52/d := (Nat.le_div_iff_mul_le hd).mpr (by rw [Nat.mul_comm]; omega)
  omega

private lemma window_limit {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun N => coneWindow (coneWidth N) d) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b+3)] with N hN
  have ha := Nat.le_mul_of_pos_right (coneWidth N) (show 0<d by omega)
  simp only [coneWindow,if_neg (show d≠1 by omega)]
  unfold coneWidth at *; omega

/-- Denominator contribution after the primitive numerator window tends to infinity. -/
noncomputable def coeff (d : ℕ) : ℝ :=
  if Odd d ∧ 3 ∣ d then
    (((2 * ∏ p∈d.primeFactors.erase 3, (1-chi p) : ℤ) : ℝ) *
      (Real.pi/(2*Real.sqrt 3) * ∏ p∈d.primeFactors.erase 3, (1-(chi p:ℝ)/p))) /
        (d*d.totient : ℝ)
  else 0

private theorem model_mean_limit {T : ℕ} (hT : 3 ≤ T) :
    Tendsto (fun V => unitMean T.factorial (fun n => (chi n:ℝ)*model T V n))
      atTop (𝓝 ((Real.pi^2/8)*∑ d∈Icc 2 T,coeff d)) := by
  have h3 : 3 ∣ T.factorial := Nat.dvd_factorial (by decide) hT
  have hdP (d : ℕ) (h : d ∈ Icc 2 T) (_ : Odd d) : d ∣ T.factorial :=
    Nat.dvd_factorial (by have := (mem_Icc.mp h).1; omega) (mem_Icc.mp h).2
  simp only [model, twisted_low_exact h3 hdP, mul_sum]
  apply tendsto_finsetSum
  intro d hd
  have h2 := (mem_Icc.mp hd).1
  by_cases H : Odd d ∧ 3 ∣ d
  · let : NeZero d := ⟨H.1.pos.ne'⟩
    simp only [dif_pos H, coeff, if_pos H, unitMean]
    have w := (weight_limit H.1.pos).div_const d
    have h := ((ThetaCharacterNumerator.row_character_numerator_limit H.1 H.2).comp (window_limit h2)).div_const (d.totient:ℝ)
    convert w.mul h using 1
    congr 1
    ring
  · simp [H, coeff]

private lemma iterated_model_limit {f : ℕ → ℝ} {g : ℕ → ℕ → ℕ → ℝ}
    {gV : ℕ → ℕ → ℝ} {gT : ℕ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop (𝓝 L))
    (hX : ∀ᶠ T : ℕ in atTop, ∀ V, Tendsto (g T V) atTop (𝓝 (gV T V)))
    (hV : ∀ᶠ T : ℕ in atTop, Tendsto (gV T) atTop (𝓝 (gT T)))
    (herr : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ᶠ V : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      |f X - g T V X| ≤ ε) : Tendsto gT atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [hX,hV,herr (ε/2) (by positivity)] with T ht hv he'
  have h := le_of_tendsto ((tendsto_const_nhds (x:=L)).sub hv).abs (he'.mono (fun V hx =>
    le_of_tendsto ((hf.sub (ht V)).abs) hx))
  rw [Real.dist_eq,abs_sub_comm]
  exact h.trans_lt (half_lt_self he)

private lemma totient_product (n : ℕ) :
    (n.totient:ℝ) = n * ∏ p∈n.primeFactors,(1-(p:ℝ)⁻¹) := by
  have H := congrArg (fun z : ℚ => (z:ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at H
  exact H

private lemma factor_identity {p : ℕ} (hp : p.Prime) (ho : Odd p) (h3 : p≠3) :
    factor true p * (1-(p:ℝ)⁻¹) = (1-(chi p:ℝ))*(1-(chi p:ℝ)/p) := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm : (p:ℝ)-1 ≠ 0 := by
    have : (1:ℝ)<p := by exact_mod_cast hp.one_lt
    linarith
  have hnd : ¬3∣p := fun h => h3 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp h).symm
  have ho' := Nat.odd_iff.mp ho
  have hmod : p%3≠0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  by_cases h5 : p%6=5
  · have hr : p%3=2 := by omega
    simp [factor,h3,h5,chi,hr]
    field_simp [hp0,hpm]
    ring
  · have hr : p%3=1 := by omega
    simp [factor,h3,h5,chi,hr]

private theorem coeff_eq_weight (d : ℕ) :
    coeff d = (Real.pi / Real.sqrt 3) * (weight true d - weight false d) := by
  by_cases hd0 : d=0
  · subst d; simp [coeff,weight]
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd0
  by_cases h3 : 3 ∣ d
  · have hm : 3∈d.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide,h3,hd0⟩
    have hz : weight false d = 0 := by
      rw [weight,prod_eq_zero hm (by norm_num [factor]),zero_div]
    rw [hz,sub_zero]
    by_cases ho : Odd d
    · have hf : ∀ p∈d.primeFactors.erase 3, factor true p*(1-(p:ℝ)⁻¹) =
          (1-(chi p:ℝ))*(1-(chi p:ℝ)/p) := by
        intro p hp
        have hh := (mem_erase.mp hp).2
        exact factor_identity (Nat.prime_of_mem_primeFactors hh)
          (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hh)) (mem_erase.mp hp).1
      have he : (∏ p∈d.primeFactors,factor true p) * (∏ p∈d.primeFactors,(1-(p:ℝ)⁻¹)) =
          (∏ p∈d.primeFactors.erase 3,(1-(chi p:ℝ))) *
            (∏ p∈d.primeFactors.erase 3,(1-(chi p:ℝ)/p)) := by
        rw [← prod_mul_distrib,← prod_erase_mul _ _ hm,← prod_mul_distrib,prod_congr rfl hf]
        norm_num [factor]
      have htot : (d.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)).ne'
      rw [coeff,if_pos (show Odd d ∧ 3 ∣ d from ⟨ho,h3⟩),weight]
      push_cast
      field_simp [htot,hd',Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3)]
      rw [totient_product]
      linear_combination (d:ℝ) * he.symm
    · have h2 : 2 ∣ d := by apply Nat.dvd_of_mod_eq_zero; have hh := Nat.mod_lt d (by decide : 0<2); by_contra! h; exact ho (Nat.odd_iff.mpr (by omega))
      have hm2 : 2∈d.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide,h2,hd0⟩
      simp [coeff,ho,weight,prod_eq_zero hm2 (by norm_num [factor] : factor true 2=0)]
  · have H : weight true d = weight false d := by
      unfold weight
      congr 1
      apply prod_congr rfl
      intro p hp
      have h : p ≠ 3 := fun e => h3 (e ▸ Nat.dvd_of_mem_primeFactors hp)
      simp only [factor,if_neg h]
    simp [coeff,h3,H]

private theorem coeff_sum_limit :
    Tendsto (fun T : ℕ => ∑ d∈Icc 2 T,coeff d) atTop
      (𝓝 (3*Real.pi/(16*Real.sqrt 3)*characterProduct)) := by
  have hs := weight_difference_hasSum.mul_left (Real.pi/Real.sqrt 3)
  have h := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hval : (Real.pi/Real.sqrt 3)*(3/16*characterProduct) =
      3*Real.pi/(16*Real.sqrt 3)*characterProduct := by ring
  rw [hval] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with T ht
  change (∑ d ∈ range (T+1),_) = _
  simp_rw [← coeff_eq_weight]
  rw [← Nat.Ico_zero_eq_range,show Icc 2 T = Ico 2 (T+1) by ext d; simp,
    ← sum_Ico_consecutive coeff (m:=0) (n:=2) (k:=T+1) (by decide) (by omega)]
  norm_num [Nat.Ico_zero_eq_range, sum_range_succ, coeff]

/-- Half of the difference between the two limiting class means. -/
noncomputable def characterConstant : ℝ := 3*Real.pi/(16*Real.sqrt 3)*characterProduct

private theorem periodic_twist (hAP : ProgressionMangoldt) {T : ℕ} (hT : 3≤T) (V : ℕ) :
    Tendsto (primeMean (fun p => (chi p:ℝ)*model T V p)) atTop
      (𝓝 (unitMean T.factorial (fun n => (chi n:ℝ)*model T V n))) := by
  apply periodic_prime_mean hAP
  have h3 : 3∣T.factorial := Nat.dvd_factorial (by decide) hT
  have hper : ThetaPeriodMeans.OnMod T.factorial (model T V) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  intro n
  change (chi (n%T.factorial):ℝ)*model T V (n%T.factorial) = (chi n:ℝ)*model T V n
  have hc : chi (n%T.factorial) = chi n := by simp only [chi,Nat.mod_mod_of_dvd _ h3]
  rw [hc,hper n]

/-- The actual prime mean of the signed modulo-three twist of the original
second-order residual equals the evaluated Euler product. -/
theorem prime_character_exact (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => (chi p:ℝ)*residual p)) atTop (𝓝 characterConstant) := by
  obtain ⟨L,_,hL⟩ := scaled_character_prime_mean hAP
    (a:=0) (fun V _ => (commonWeight_bounds (2*V^52) 3).1)
  have hlim := iterated_model_limit hL
    ((eventually_ge_atTop 3).mono fun T ht => periodic_twist hAP ht)
    ((eventually_ge_atTop 3).mono fun T ht => model_mean_limit ht)
    (fun ε he => twisted_approx_eventually he)
  have heq := tendsto_nhds_unique hlim (coeff_sum_limit.const_mul (Real.pi^2/8))
  have h := residual_twist hAP hL
  rw [heq] at h
  convert h using 2
  unfold characterConstant
  field_simp [Real.pi_ne_zero]

/-- Both ordinary class averages and the limiting variance of the original
residual, with the full modulo-three bias evaluated. -/
theorem prime_class_statistics_exact (hAP : ProgressionMangoldt) :
    ∃ V : ℝ, characterConstant^2 ≤ V ∧
      Tendsto (classMean 1 residual) atTop (𝓝 (diagonalConstant+characterConstant)) ∧
      Tendsto (classMean 2 residual) atTop (𝓝 (diagonalConstant-characterConstant)) ∧
      Tendsto (sampleVariance residual) atTop (𝓝 V) := by
  obtain ⟨C,hC,hc,h1,h2⟩ := S_class_prime_means hAP
  have heq := tendsto_nhds_unique hc (prime_character_exact hAP)
  obtain ⟨D,V,_,hV,hD1,_,_,hv⟩ := S_prime_class_statistics hAP
  have hCD := tendsto_nhds_unique h1 hD1
  have hDC : D = characterConstant := by linarith
  exact ⟨V,hDC ▸ hV,heq ▸ h1,heq ▸ h2,hv⟩

#print axioms prime_character_exact
#print axioms prime_class_statistics_exact

end Arxiv.«2501.03234».ThetaCharacterCoefficient
