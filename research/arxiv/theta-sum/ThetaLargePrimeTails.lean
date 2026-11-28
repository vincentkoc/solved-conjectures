import ThetaLargeLawTails

/-! Quantitative all-prime lower fractions above and below arbitrary high thresholds. -/
namespace Arxiv.«2501.03234».ThetaLargePrimeTails
open Finset Filter MeasureTheory ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeDensity
open ThetaDiagonalConstant ThetaPrimeLaw ThetaProfiniteUnits ThetaDyadicLaw ThetaUnboundedExcursions
open scoped Topology

private theorem count_open (hAP : ProgressionMangoldt) {k r : ℕ} (hr : r.Coprime (2^k)) (hlt : r<2^k)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {U : Set ℝ} (hU : IsOpen U) {e : ℝ} (he : 0< e)
    (hm : ENNReal.ofReal e ≤ (haarLaw F : Measure ℝ) U) : ∀ᶠ X : ℕ in atTop,
      (e/(4*((2^k).totient:ℝ)))*X.primeCounting ≤ ((primeSet (fun p => p%2^k=r ∧ residual p∈U) X).card:ℝ) := by
  let q := 2^k
  have hq : 0< q := by dsimp [q]; positivity
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hut := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (progression_law_tendsto hAP hr hlt hF) hU
  have hz : ENNReal.ofReal (e/2)< ENNReal.ofReal e := (ENNReal.ofReal_lt_ofReal_iff he).mpr (half_lt_self he)
  have hfrac : 1/(2*(q.totient:ℝ)) < 1/q.totient := one_div_lt_one_div_of_lt hφ (by linarith)
  filter_upwards [(class_prime_density hAP hq hr hlt).eventually_const_lt hfrac,
    eventually_lt_of_lt_liminf ((hz.trans_le hm).trans_le hut),class_nonempty hAP hq hr hlt,
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting).eventually_gt_atTop 0] with X hd ha hx hc
  have hr' := (ENNReal.ofReal_lt_iff_lt_toReal (half_pos he).le (measure_ne_top _ _)).mp ha
  change e/2 < (progressionLaw q r residual X : Measure ℝ).real U at hr'
  rw [relative_count hx U hU.measurableSet] at hr'
  have hcard : (0:ℝ)<(primeSet (fun p => p%q=r) X).card := by exact_mod_cast card_pos.mpr hx
  have H := mul_le_mul_of_nonneg_left ((lt_div_iff₀ (by exact hc : (0:ℝ)< X.primeCounting)).mp hd).le (half_pos he).le
  apply le_trans _ (H.trans ((lt_div_iff₀ hcard).mp hr').le)
  change e/(4*(q.totient:ℝ))*X.primeCounting ≤ e/2*(1/(2*(q.totient:ℝ))*X.primeCounting)
  exact le_of_eq (by ring)

/-- For every sufficiently large height, a quantitative fraction of all primes lies
in either tail in each fixed reduced dyadic class. The endpoint may depend on the class and height. -/
theorem counts (hAP : ProgressionMangoldt) : ∀ᶠ b : ℝ in atTop,
    ∀ k r : ℕ, r.Coprime (2^k) → r<2^k → ∀ᶠ X : ℕ in atTop,
      let d := Real.exp (-(Real.exp (32*Real.pi*Real.sqrt b)))/(4*((2^k).totient:ℝ))
      d*X.primeCounting ≤ ((primeSet (fun p => p%2^k=r ∧ diagonalConstant+b<(S p:ℝ)/p-Real.log p/2) X).card:ℝ) ∧
      d*X.primeCounting ≤ ((primeSet (fun p => p%2^k=r ∧ (S p:ℝ)/p-Real.log p/2< diagonalConstant-b) X).card:ℝ) := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  filter_upwards [ThetaLargeLawTails.tails hAP] with b H
  intro k r hr hlt
  obtain ⟨h₁,h₂⟩ := H F hF
  exact (count_open hAP hr hlt hF isOpen_Ioi (Real.exp_pos _) h₁).and
    (count_open hAP hr hlt hF isOpen_Iio (Real.exp_pos _) h₂)
#print axioms counts
end Arxiv.«2501.03234».ThetaLargePrimeTails
