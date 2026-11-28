import ThetaCharacterSeven
import ThetaCharacterCoefficient

/-! A second independent signed prime correlation for the original theta residual. -/
namespace Arxiv.«2501.03234».ThetaSevenPrimeBias
open Finset Filter ThetaCharacterSeven ThetaRowCorrelations ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans
open ThetaConditionalRows ThetaReciprocalInversion ThetaReciprocalBlocks ThetaPrimeTailTransfer ThetaPeriodMeans
open ThetaCharacterCoefficient ThetaDiagonalConstant ThetaPrimeMeanSquare
open scoped Topology

/-- The negatively oriented quadratic character modulo seven. -/
def sevenWeight (n : ℕ) : ℝ := -(chi7 n:ℝ)

theorem weight_bound (n : ℕ) : |sevenWeight n| ≤ 1 := by
  unfold sevenWeight chi7
  split_ifs <;> norm_num

theorem weight_period : OnMod 7 sevenWeight := by intro n; simp [sevenWeight,chi7]

theorem weight_mean : unitMean 7 sevenWeight=0 := by
  rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,sum_filter]
  norm_num [sum_range_succ,Nat.Coprime,sevenWeight,chi7]

private lemma product_onMod {d e P : ℕ} (hd : d∣P) (he : e∣P)
    {f g : ℕ → ℝ} (hf : OnMod d f) (hg : OnMod e g) : OnMod P (fun p => f p*g p) := by
  intro n
  exact congrArg₂ (·*·) (onMod_lift hd hf n) (onMod_lift he hg n)

private lemma row_descent {P d : ℕ} [NeZero P] [NeZero d] (hd : d∣P) (h7 : 7∣d) (K : ℕ) :
    unitMean P (fun n => sevenWeight n*row d K n)=unitMean d (fun n => sevenWeight n*row d K n) :=
  unitMean_lift hd (product_onMod h7 (dvd_refl _) weight_period (row_onMod d K))

private lemma row_nonneg {P d : ℕ} [NeZero P] [NeZero d] (hd : d∣P) (hP : 7∣P) (ho : Odd d) (K : ℕ) :
    0 ≤ unitMean P (fun n => sevenWeight n*row d K n) := by
  by_cases h7 : 7∣d
  · rw [row_descent hd h7 K]
    simp only [unitMean,sevenWeight,neg_mul,sum_neg_distrib]
    exact div_nonneg (neg_nonneg.mpr (row_transform_nonpos ho h7 K)) (Nat.cast_nonneg _)
  · have hc := (show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr h7
    rw [unitMean_lift (hc.mul_dvd_of_dvd_of_dvd hP hd) (product_onMod (Nat.dvd_mul_right 7 d)
      (Nat.dvd_mul_left d 7) weight_period (row_onMod d K)),unitMean_mul hc weight_period (row_onMod d K),
      weight_mean,zero_mul]

private theorem model_prime_lower (hAP : ProgressionMangoldt) {T V : ℕ} (hT : 21≤T) (hV : 1344≤V) :
    ∃ L : ℝ, commonWeight (2*V^52) 7/36+commonWeight (2*V^52) 21/81 ≤ L ∧
      Tendsto (primeMean (fun p => sevenWeight p*model T V p)) atTop (𝓝 L) := by
  let M := T.factorial
  let : NeZero M := ⟨(Nat.factorial_pos T).ne'⟩
  let K := coneWindow (coneWidth V)
  let a := commonWeight (2*V^52)
  have hd (d : ℕ) (h : d ∈ Icc 2 T) (_ : Odd d) : d ∣ M :=
    Nat.dvd_factorial (by have := (mem_Icc.mp h).1; omega) (mem_Icc.mp h).2
  have hper : OnMod M (model T V) := low_onMod hd _ _
  have h7 : 7 ∣ M := Nat.dvd_factorial (by decide) (by omega)
  refine ⟨_,?_,periodic_prime_mean hAP (product_onMod h7 (dvd_refl M) weight_period hper)⟩
  let b (d : ℕ) := (a d/d)*unitMean M (fun n => sevenWeight n*row d (K d) n)
  have hb (d) (hh : d∈Icc 2 T) : 0≤b d := by
    dsimp only [b]
    by_cases ho : Odd d
    · let : NeZero d := ⟨ho.pos.ne'⟩
      exact mul_nonneg (div_nonneg (commonWeight_bounds _ _).1 (Nat.cast_nonneg _))
        (row_nonneg (hd d hh ho) h7 ho _)
    · simp [even_row ho,unitMean]
  have hK7 : 448≤K 7 := by dsimp [K,coneWindow,coneWidth]; omega
  have hK21 : 1344≤K 21 := by dsimp [K,coneWindow,coneWidth]; omega
  have hrow7 : 7/36≤unitMean M (fun n => sevenWeight n*row 7 (K 7) n) := by
    rw [row_descent h7 (dvd_refl 7)]
    simp only [unitMean,sevenWeight,neg_mul,sum_neg_distrib]
    rw [show Nat.totient 7=6 by decide]
    norm_num only [Nat.cast_ofNat,le_div_iff₀ (by norm_num : (0:ℝ)<6)]
    linarith only [seven_row_bound hK7]
  have hrow21 : 21/81≤unitMean M (fun n => sevenWeight n*row 21 (K 21) n) := by
    have hd21 : 21∣M := Nat.dvd_factorial (by decide) hT
    rw [row_descent hd21 (by decide)]
    simp only [unitMean,sevenWeight,neg_mul,sum_neg_distrib]
    rw [show Nat.totient 21=12 by decide]
    norm_num only [Nat.cast_ofNat,le_div_iff₀ (by norm_num : (0:ℝ)<12)]
    linarith only [twentyone_row_bound hK21]
  change a 7/36+a 21/81 ≤ unitMean M (fun n => sevenWeight n*low T K a n)
  rw [mean_low]
  have hs : ({7,21}:Finset ℕ) ⊆ Icc 2 T := by
    intro d hd'
    simp only [mem_insert,mem_singleton] at hd'
    rcases hd' with rfl|rfl <;> exact mem_Icc.mpr ⟨by decide,by omega⟩
  have H := sum_le_sum_of_subset_of_nonneg (f:=b) hs (fun d hd' _ => hb d hd')
  rw [sum_insert (by decide : 7∉({21}:Finset ℕ)),sum_singleton] at H
  apply le_trans _ H
  have h₇ := mul_le_mul_of_nonneg_left hrow7 (div_nonneg (commonWeight_bounds (2*V^52) 7).1 (by norm_num : (0:ℝ)≤7))
  have h₂₁ := mul_le_mul_of_nonneg_left hrow21 (div_nonneg (commonWeight_bounds (2*V^52) 21).1 (by norm_num : (0:ℝ)≤21))
  dsimp only [b,a]
  norm_num only [Nat.cast_ofNat]
  linarith only [h₇,h₂₁]

private lemma scaled_limit_from_cutoff (hAP : ProgressionMangoldt) {a : ℝ} (ha : a < Real.pi^2/8) :
    ∃ L : ℝ, (13/324)*a ≤ L ∧ Tendsto (primeMean (fun p => sevenWeight p*scaledOff p)) atTop (𝓝 L) := by
  apply limit_of_prime_models
  intro ε he
  obtain ⟨T,hT,H⟩ := ((eventually_ge_atTop 21).and (bounded_twist_approx_eventually sevenWeight weight_bound he)).exists
  have hweight := (commonWeight_limit (d:=7) (by decide)).eventually_const_lt ha
  have hweight21 := (commonWeight_limit (d:=21) (by decide)).eventually_const_lt ha
  obtain ⟨V,hV,hW,hW21,h⟩ := ((eventually_ge_atTop 1344).and (hweight.and (hweight21.and H))).exists
  obtain ⟨L,hL,hl⟩ := model_prime_lower hAP hT hV
  exact ⟨_,L,by linarith only [hW,hW21,hL],hl,h⟩

/-- The conductors three and seven detect distinct signed components of the
residual. The negatively oriented modulo-seven correlation is at least 13/324. -/
theorem seven_prime_bias (hAP : ProgressionMangoldt) :
    ∃ D : ℝ, 13/324 ≤ D ∧ Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D) := by
  obtain ⟨L,_,hL⟩ := scaled_limit_from_cutoff hAP (a:=0) (by positivity)
  have hlim : Real.pi^2/8 ≤ (324/13)*L := by
    by_contra! hn
    let a := ((324/13)*L+Real.pi^2/8)/2
    have ha : a < Real.pi^2/8 := by dsimp [a]; linarith
    obtain ⟨L',hL',hf⟩ := scaled_limit_from_cutoff hAP ha
    have heq := tendsto_nhds_unique hf hL
    dsimp only [a] at hL'
    linarith
  have hmean : Tendsto (primeMean sevenWeight) atTop (𝓝 0) := by
    simpa only [weight_mean] using periodic_prime_mean hAP weight_period
  refine ⟨_,?_,bounded_residual_twist sevenWeight weight_bound hmean hL⟩
  rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity : 0<Real.pi^2)]
  linarith only [hlim]

#print axioms seven_prime_bias

/-- A periodic model whose period omits seven makes a positive irreducible
mean absolute error on the original residual, regardless of the model values. -/
theorem seven_periodic_gap (hAP : ProgressionMangoldt) {m : ℕ} [NeZero m] (hm : ¬7∣m)
    {g : ℕ → ℝ} (hg : OnMod m g) {a : ℝ} (ha : a < 13/324) :
    ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |residual p-g p|) X := by
  obtain ⟨D,hD,h⟩ := seven_prime_bias hAP
  have hc := (show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr hm
  have hper := product_onMod (Nat.dvd_mul_right 7 m) (Nat.dvd_mul_left m 7) weight_period hg
  have h0 := periodic_prime_mean hAP hper
  rw [unitMean_mul hc weight_period hg,weight_mean,zero_mul] at h0
  have H := h.sub h0
  rw [sub_zero] at H
  filter_upwards [H.eventually_const_lt (ha.trans_le hD)] with X hX
  apply hX.trans_le
  rw [primeMean,primeMean,primeMean,← sub_div,← sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro p _
  rw [← mul_sub]
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (weight_bound p))

#print axioms seven_periodic_gap

end Arxiv.«2501.03234».ThetaSevenPrimeBias
