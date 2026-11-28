import ThetaLegendreFactors
import ThetaCharacterCoefficient
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Quadratic prime correlations and the obstruction to every fixed congruence model. -/
namespace Arxiv.«2501.03234».ThetaPrimeSpectrum
open Finset Filter Topology ThetaLegendreFactors ThetaRowCorrelations ThetaNaturalPrimeMeans
open ThetaCharacterPrimeMeans ThetaConditionalRows ThetaReciprocalInversion ThetaReciprocalBlocks
open ThetaPrimeTailTransfer ThetaPeriodMeans ThetaCharacterCoefficient ThetaDiagonalConstant ThetaPrimeMeanSquare
open ThetaCharacterSeven (siftedSum)
local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos n).ne'⟩
variable (q : ℕ) [Fact q.Prime]

private noncomputable abbrev w (n : ℕ) : ℝ := (symbol q n:ℝ)

private lemma bounded (n : ℕ) : |w q n| ≤ 1 := by
  by_cases h : q∣n
  · simp [w,symbol_zero q h]
  · rcases symbol_unit q h with h|h <;> simp [w,h]

private lemma onMod : OnMod q (w q) := fun n => congrArg (Int.cast (R:=ℝ)) (symbol_mod q (dvd_refl q) n)

private lemma centered (hq : q≠2) : unitMean q (w q) = 0 := by
  rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,sum_filter]
  have he (j : ℕ) : (if j.Coprime q then w q j else 0)=w q j := by
    by_cases h : j.Coprime q
    · simp [h]
    · have hd : q∣j := by by_contra hn; exact h ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hn).symm
      simp [h,w,symbol_zero q hd]
  simp_rw [he]
  have hz := congrArg (Int.cast (R:=ℝ)) (range_zero q hq)
  push_cast at hz
  rw [show (∑ j ∈ range q,w q j)=0 from hz,zero_div]

private lemma product_onMod {d e P : ℕ} (hd : d∣P) (he : e∣P)
    {f g : ℕ → ℝ} (hf : OnMod d f) (hg : OnMod e g) : OnMod P (fun n => f n*g n) :=
  fun n => congrArg₂ (·*·) (onMod_lift hd hf n) (onMod_lift he hg n)

private theorem periodic_model (hAP : ProgressionMangoldt) {T : ℕ} (ht : q≤T) (V : ℕ) :
    Tendsto (primeMean (fun n => w q n*model T V n)) atTop
      (𝓝 (unitMean T.factorial (fun n => w q n*model T V n))) := by
  apply periodic_prime_mean hAP
  apply product_onMod (Nat.dvd_factorial (Fact.out : q.Prime).pos ht) (dvd_refl _) (onMod q)
  apply low_onMod
  intro d hd _
  exact Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2

/-- Nonnegative denominator weight after the signed conductor factor is taken out. -/
noncomputable def amplitude (d : ℕ) : ℝ :=
  if Odd d ∧ q∣d then
    (∏ p∈d.primeFactors.erase q,(1-w q p)) *
      (∏ p∈insert 2 (d.primeFactors.erase q),(1-w q p/p)) / ((d:ℝ)*d.totient) else 0

theorem amplitude_nonneg (d : ℕ) : 0 ≤ amplitude q d := by
  unfold amplitude
  split_ifs
  · apply div_nonneg _ (by positivity)
    apply mul_nonneg
    · exact prod_nonneg (fun p _ => sub_nonneg.mpr ((le_abs_self _).trans (bounded q p)))
    · apply prod_nonneg
      intro p hp
      have hpr : p.Prime := (mem_insert.mp hp).elim (fun h => h ▸ Nat.prime_two)
        (fun h => Nat.prime_of_mem_primeFactors (mem_erase.mp h).2)
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hpr.one_le
      apply sub_nonneg.mpr
      rw [div_le_iff₀ (by positivity : (0:ℝ)<p),one_mul]
      exact ((le_abs_self _).trans (bounded q p)).trans hp1
  · exact le_rfl

theorem conductor_amplitude (ho : Odd q) :
    amplitude q q = (1-(symbol q 2:ℝ)/2)/((q:ℝ)*q.totient) := by
  simp [amplitude,ho,(Fact.out : q.Prime).primeFactors]

private theorem conductor_pos (ho : Odd q) : 0 < amplitude q q := by
  rw [conductor_amplitude q ho]
  have H := (le_abs_self _).trans (bounded q 2)
  have hp : 0 < q.totient := Nat.totient_pos.mpr (Fact.out : q.Prime).pos
  have hq0 := (Fact.out : q.Prime).pos
  exact div_pos (by linarith) (by positivity)

private theorem row_lim {P d : ℕ} [NeZero P] [NeZero d] (hP : q∣P) (hd : d∣P)
    (hq : q≠2) {L : ℝ} (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) :
    Tendsto (fun K => unitMean P (fun n => w q n*row d K n)/(d:ℝ)) atTop
      (𝓝 ((parityFactor q:ℝ)*L*amplitude q d)) := by
  by_cases H : Odd d ∧ q∣d
  · have he (K : ℕ) : unitMean P (fun n => w q n*row d K n) = unitMean d (fun n => w q n*row d K n) :=
      unitMean_lift hd (product_onMod H.2 (dvd_refl d) (onMod q) (row_onMod d K))
    simp_rw [he,unitMean]
    have h := ((row_limit q H.1 H.2 hL).div_const (d.totient:ℝ)).div_const (d:ℝ)
    convert h using 1
    congr 1
    simp only [amplitude,if_pos H,Int.cast_mul,Int.cast_prod,Int.cast_sub,Int.cast_one,w]
    ring
  · rw [amplitude,if_neg H,mul_zero]
    have he (K : ℕ) : unitMean P (fun n => w q n*row d K n)=0 := by
      by_cases ho : Odd d
      · have hc := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun hh => H ⟨ho,hh⟩)
        rw [unitMean_lift (hc.mul_dvd_of_dvd_of_dvd hP hd) (product_onMod (Nat.dvd_mul_right q d)
          (Nat.dvd_mul_left d q) (onMod q) (row_onMod d K)),unitMean_mul hc (onMod q) (row_onMod d K),
          centered q hq,zero_mul]
      · simp [even_row ho,unitMean]
    simpa only [he,zero_div] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=atTop (α:=ℕ)))

private theorem model_limit {T : ℕ} (ht : q≤T) (hq : q≠2)
    {L : ℝ} (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) :
    Tendsto (fun V => unitMean T.factorial (fun n => w q n*model T V n)) atTop
      (𝓝 ((Real.pi^2/8)*((parityFactor q:ℝ)*L)*∑ d∈Icc 2 T,amplitude q d)) := by
  simp only [model,mean_low,mul_sum]
  apply tendsto_finsetSum
  intro d hd
  have h2 := (mem_Icc.mp hd).1
  let : NeZero d := ⟨by omega⟩
  have hP := Nat.dvd_factorial (Fact.out : q.Prime).pos ht
  have hPd := Nat.dvd_factorial (by omega : 0<d) (mem_Icc.mp hd).2
  have H := (commonWeight_limit (d:=d) (by omega)).mul ((row_lim q hP hPd hq hL).comp (window_limit h2))
  convert H using 1
  · funext V; dsimp only [Function.comp_apply]; ring
  · congr 1; ring

private theorem transfer (hAP : ProgressionMangoldt) (hq : q ≠ 2)
    {L : ℝ} (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) :
    ∃ C : ℝ, Tendsto (primeMean (fun p => w q p*residual p)) atTop (𝓝 C) ∧
      Tendsto (fun T => (parityFactor q:ℝ)*L*∑ d∈Icc 2 T,amplitude q d) atTop (𝓝 C) := by
  obtain ⟨A,hA⟩ := limit_of_approximants (f:=primeMean (fun p => w q p*scaledOff p)) (fun ε he => by
    obtain ⟨T,hT,H⟩ := ((eventually_ge_atTop q).and (bounded_twist_approx_eventually _ (bounded q) he)).exists
    obtain ⟨V,hV⟩ := H.exists
    exact ⟨_,_,periodic_model q hAP hT V,hV⟩)
  have hlim := iterated_model_limit hA
    ((eventually_ge_atTop q).mono fun T ht => periodic_model q hAP ht)
    ((eventually_ge_atTop q).mono fun T ht => model_limit q ht hq hL)
    (fun ε he => bounded_twist_approx_eventually _ (bounded q) he)
  have hw := periodic_prime_mean hAP (onMod q)
  rw [centered q hq] at hw
  refine ⟨_,bounded_residual_twist _ (bounded q) hw hA,?_⟩
  apply ((hlim.const_mul (8/Real.pi^2))).congr'
  filter_upwards with T
  field_simp [Real.pi_ne_zero]

/-- Every prime conductor q ≡ 3 mod 4 has a nonzero ordinary prime correlation with the
original residual. The magnitude dominates the individual conductor row. -/
theorem prime_correlation (hAP : ProgressionMangoldt) (hq : q%4=3) :
    ∃ L C : ℝ, 0 < L ∧ Tendsto (siftedSum (term q) ∅) atTop (𝓝 L) ∧
      Tendsto (primeMean (fun p => (symbol q p:ℝ)*residual p)) atTop (𝓝 C) ∧ C ≠ 0 ∧
      0 < (parityFactor q:ℝ)*C ∧
      |(parityFactor q:ℝ)*L| *amplitude q q ≤ |C| ∧
      Tendsto (fun T => (parityFactor q:ℝ)*L*∑ d∈Icc 2 T,amplitude q d) atTop (𝓝 C) := by
  have h2 : q≠2 := by omega
  obtain ⟨L,hLn,hL⟩ := reciprocal_limit q h2
  obtain ⟨C,hC,hlim⟩ := transfer q hAP h2 hL
  have H : |(parityFactor q:ℝ)*L| *amplitude q q ≤ |C| := by
    apply ge_of_tendsto hlim.abs
    filter_upwards [eventually_ge_atTop q] with T hT
    rw [abs_mul ((parityFactor q:ℝ)*L) (∑ d∈Icc 2 T,amplitude q d),abs_of_nonneg (sum_nonneg fun d _ => amplitude_nonneg q d)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact single_le_sum (fun d _ => amplitude_nonneg q d)
      (mem_Icc.mpr ⟨(Fact.out : q.Prime).two_le,hT⟩ : q∈Icc 2 T)
  have ha := conductor_pos q (Nat.odd_iff.mpr (by omega))
  have hf : (parityFactor q:ℝ) ≠ 0 := by exact_mod_cast parityFactor_nonzero q hq
  have hbound : (parityFactor q:ℝ)^2*L*amplitude q q ≤ (parityFactor q:ℝ)*C := by
    apply ge_of_tendsto (hlim.const_mul (parityFactor q:ℝ))
    filter_upwards [eventually_ge_atTop q] with T hT
    have hsum := single_le_sum (fun d _ => amplitude_nonneg q d)
      (mem_Icc.mpr ⟨(Fact.out : q.Prime).two_le,hT⟩ : q∈Icc 2 T)
    have h := mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg (parityFactor q:ℝ)) hLn.le)
    linarith only [h]
  have hpos := (mul_pos (mul_pos (sq_pos_of_ne_zero hf) hLn) ha).trans_le hbound
  exact ⟨L,C,hLn,hL,hC,abs_pos.mp ((mul_pos (abs_pos.mpr (mul_ne_zero hf hLn.ne')) ha).trans_le H),
    hpos,H,hlim⟩

/-- Every other odd prime conductor has zero correlation by reflection. -/
theorem even_character_mean (hAP : ProgressionMangoldt) (hq : q%4=1) :
    Tendsto (primeMean (fun p => (symbol q p:ℝ)*residual p)) atTop (𝓝 0) := by
  have h2 : q≠2 := by omega
  obtain ⟨L,_,hL⟩ := reciprocal_limit q h2
  obtain ⟨C,hC,hlim⟩ := transfer q hAP h2 hL
  simp only [parityFactor_zero q hq,Int.cast_zero,zero_mul] at hlim
  have HC := tendsto_nhds_unique hlim (tendsto_const_nhds (x:=(0:ℝ)))
  exact HC ▸ hC

/-- The classical Dirichlet quadratic-excess formula supplies a residue-class sign and
a lower bound in terms of the square of the excess. The formula is an explicit premise. -/
theorem of_quadratic_excess_formula (hAP : ProgressionMangoldt) (hq : q%4=3)
    (H : ℤ) (hex : H=∑ j∈range (q/2),symbol q (j+1))
    (hDir : ∀ L : ℝ, Tendsto (siftedSum (term q) ∅) atTop (𝓝 L) →
      (H:ℝ) = (2-(symbol q 2:ℝ))*Real.sqrt q*L/Real.pi) :
    ∃ C : ℝ, Tendsto (primeMean (fun p => (symbol q p:ℝ)*residual p)) atTop (𝓝 C) ∧
      0 < -(symbol q 2:ℝ)*C ∧ Real.pi*(H:ℝ)^2/(Real.sqrt q*((q:ℝ)*q.totient)) ≤ |C| := by
  have ho := Nat.odd_iff.mpr (show q%2=1 by omega)
  have hn : ¬q∣2 := by
    have hq2 : 2<q := by omega
    exact Nat.not_dvd_of_pos_of_lt (by decide) hq2
  obtain ⟨L,C,hL,hlim,hC,_,hpos,hbound,_⟩ := prime_correlation q hAP hq
  have hD := hDir L hlim
  have hP := parityFactor_eq_excess q ho
  rw [← hex] at hP
  rw [hP,Int.cast_mul,Int.cast_mul] at hpos hbound
  rw [conductor_amplitude q ho] at hbound
  have hq0 := (Fact.out : q.Prime).pos
  have hsq : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hq0)
  have hχ := symbol_unit q hn
  refine ⟨C,hC,?_,?_⟩
  · rcases hχ with h|h <;> rw [h] at hD hpos ⊢ <;> push_cast at hD hpos ⊢ <;>
      have hH : 0<(H:ℝ) := hD ▸ (by positivity) <;> nlinarith
  · rcases hχ with h|h <;> rw [h] at hD hbound <;> push_cast at hD hbound <;>
      have hH : 0<(H:ℝ) := hD ▸ (by positivity) <;> apply le_trans _ hbound <;>
      rw [abs_mul,abs_of_pos hL] <;>
      simp only [abs_mul,abs_neg,abs_of_pos hH,abs_one,mul_one] <;>
      apply le_of_eq <;> field_simp [hsq.ne',Real.pi_ne_zero] at hD ⊢ <;> norm_num at hD ⊢ <;> nlinarith

/-- Pairwise orthogonality of distinct odd prime Legendre characters under the
ordinary prime mean, with unit diagonal. -/
theorem prime_character_pair (hAP : ProgressionMangoldt) (hq : q≠2) (r : ℕ) [Fact r.Prime] :
    Tendsto (primeMean (fun p => (symbol q p:ℝ)*(symbol r p:ℝ))) atTop (𝓝 (if q=r then 1 else 0)) := by
  by_cases he : q=r
  · subst r
    rw [if_pos rfl]
    have ht := periodic_prime_mean hAP (product_onMod (dvd_refl q) (dvd_refl q) (onMod q) (onMod q))
    have hv (u : (ZMod q)ˣ) : w q (u:ZMod q).val * w q (u:ZMod q).val=1 := by
      have hn := (Fact.out : q.Prime).coprime_iff_not_dvd.mp (ZMod.val_coe_unit_coprime u).symm
      rcases symbol_unit q hn with h|h <;> norm_num [w,h]
    have hφ := (Nat.totient_pos.mpr (Fact.out : q.Prime).pos).ne'
    simpa only [unitMean,hv,sum_const,card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul,mul_one,
      div_self (by exact_mod_cast hφ : (q.totient:ℝ)≠0)] using ht
  · rw [if_neg he]
    have hc := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun hd =>
      he ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : r.Prime)).mp hd))
    have ht := periodic_prime_mean hAP (product_onMod (Nat.dvd_mul_right q r) (Nat.dvd_mul_left r q)
      (onMod q) (onMod r))
    rwa [unitMean_mul hc (onMod q) (onMod r),centered q hq,zero_mul] at ht

#print axioms prime_character_pair

/-- A correlation at a conductor coprime to the period gives a lower bound for the
ordinary prime mean of the absolute approximation error. -/
theorem periodic_error_of_correlation (hAP : ProgressionMangoldt) {m : ℕ} [NeZero m]
    (hc : q.Coprime m) (hodd : q≠2) {C : ℝ}
    (hC : Tendsto (primeMean (fun p => (symbol q p:ℝ)*residual p)) atTop (𝓝 C))
    {g : ℕ → ℝ} (hg : OnMod m g) {a : ℝ} (ha : a < |C|) :
    ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |residual p-g p|) X := by
  have hper := product_onMod (Nat.dvd_mul_right q m) (Nat.dvd_mul_left m q) (onMod q) hg
  have h0 := periodic_prime_mean hAP hper
  rw [unitMean_mul hc (onMod q) hg,centered q hodd,zero_mul] at h0
  have H := hC.sub h0
  rw [sub_zero] at H
  filter_upwards [H.abs.eventually_const_lt ha] with X hX
  apply hX.trans_le
  simp only [primeMean,← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) X.primeCounting)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (abs_sum_le_sum_abs ..).trans (sum_le_sum fun p _ => ?_)
  rw [← mul_sub,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (bounded q p)

/-- For every fixed modulus, a positive absolute-mean error persists for every choice
of values in its residue classes. The lower bound is independent of the model. -/
theorem fixed_period_gap (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ δ : ℝ, 0<δ ∧ ∀ g : ℕ → ℝ, OnMod m g → ∀ a < δ,
      ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |residual p-g p|) X := by
  obtain ⟨q,hqm,hpr,hq⟩ := Nat.forall_exists_prime_gt_and_modEq m (q:=4) (a:=3) (by decide) (by decide)
  let : Fact q.Prime := ⟨hpr⟩
  have hq3 : q%4=3 := hq
  obtain ⟨_,C,_,_,hC,hC0,_⟩ := prime_correlation q hAP hq3
  refine ⟨|C|,abs_pos.mpr hC0,?_⟩
  intro g hg a ha
  exact periodic_error_of_correlation q hAP
    (hpr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos m) hqm)) (by omega) hC hg ha

#print axioms amplitude_nonneg
#print axioms conductor_amplitude
#print axioms of_quadratic_excess_formula
#print axioms even_character_mean
#print axioms prime_correlation
#print axioms periodic_error_of_correlation
#print axioms fixed_period_gap
end Arxiv.«2501.03234».ThetaPrimeSpectrum
