import ThetaIdentityPrimeMeans

/-! The centered original prime theta sum has an unbounded law in both directions. -/
namespace Arxiv.«2501.03234».ThetaUnboundedExcursions
open Finset Filter MeasureTheory ThetaIdentityPrimeMeans ThetaPrimeLaw ThetaProfiniteUnits
open ThetaDyadicLaw ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeDensity ThetaDiagonalConstant
open scoped Topology NNReal
noncomputable section

private theorem class_positive (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0< q) (hr : r.Coprime q) (hlt : r< q) :
    PositiveLowerPrimeDensity (fun p => p%q=r) := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  let c := 1/(q.totient:ℝ)
  have hc : 0< c := by dsimp [c]; positivity
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [(class_prime_density hAP hq hr hlt).eventually_const_lt (half_lt_self hc),
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting).eventually_gt_atTop 0] with X h hx
  exact ((lt_div_iff₀ (by exact hx : (0:ℝ)< X.primeCounting)).mp h).le

private theorem upper_closed (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) (b : ℝ) : 0<(haarLaw F : Measure ℝ) (Set.Ici b) := by
  obtain ⟨m,hm,L,hb,hL⟩ := arbitrarily_large hAP b
  have hd := above_mean_density (fun p => p%m=1) (class_positive hAP (by omega) (Nat.coprime_one_left _) hm)
    (s:=1) (by norm_num) hb (by
      apply hL.congr'
      exact Eventually.of_forall fun X => by simp only [progressionMean,predicateMean,one_mul])
  apply positive_mass_of_density isClosed_Ici (empirical_tendsto hAP hF) hd
  intro p _ h; exact (by simpa only [one_mul] using h.2 : b< residual p).le

/-- The common law gives positive mass to both open tails at every real threshold. -/
theorem unbounded_law (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) (b : ℝ) :
    0<(haarLaw F : Measure ℝ) (Set.Ioi b) ∧ 0<(haarLaw F : Measure ℝ) (Set.Iio b) := by
  constructor
  · exact (upper_closed hAP hF (b+1)).trans_le (measure_mono (fun x hx => by change b< x; change b+1≤ x at hx; linarith))
  · let f (x : ℝ) := 2*diagonalConstant-x
    have hm : Measurable f := by dsimp [f]; fun_prop
    calc 0 < (haarLaw F : Measure ℝ) (Set.Ici (2*diagonalConstant-b+1)) := upper_closed hAP hF _
         _ ≤ (haarLaw F : Measure ℝ) (f ⁻¹' Set.Iio b) := measure_mono (fun x hx => by
            change 2*diagonalConstant-x< b; change 2*diagonalConstant-b+1≤ x at hx; linarith)
         _ = (reflectedLaw diagonalConstant (haarLaw F) : Measure ℝ) (Set.Iio b) := by
            rw [reflectedLaw,ProbabilityMeasure.toMeasure_map,Measure.map_apply hm measurableSet_Iio]
         _ = _ := by rw [law_symmetric hAP hF]

theorem relative_count {q r X : ℕ} (hx : (primeSet (fun n => n%q=r) X).Nonempty)
    (U : Set ℝ) (hU : MeasurableSet U) :
    (progressionLaw q r residual X : Measure ℝ).real U =
       ((primeSet (fun p => p%q=r ∧ residual p∈U) X).card:ℝ)/(primeSet (fun p => p%q=r) X).card := by
  classical
  rw [←integral_indicator_one hU,progression_integral hx residual (measurable_one.indicator hU)]
  simp only [progressionMean,Set.indicator_apply,Pi.one_apply,sum_boole]
  have he : ((primeSet (fun n => n%q=r) X).filter (fun p => residual p∈U)) =
      primeSet (fun p => p%q=r ∧ residual p∈U) X := by
    ext p; simp only [primeSet,mem_filter]; tauto
  rw [he]

/-- Every open set of positive limiting mass has positive lower density in
any reduced dyadic prime class, with all primes in the denominator. -/
theorem dyadic_open_density (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {k r : ℕ} (hr : r.Coprime (2^k)) (hlt : r<2^k) {U : Set ℝ}
    (hU : IsOpen U) (hμ : 0<(haarLaw F : Measure ℝ) U) :
    PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ residual p∈U) := by
  let q := 2^k
  let μ : Measure ℝ := haarLaw F
  let z := μ.real U/2
  have hR : 0<μ.real U := ENNReal.toReal_pos hμ.ne' (measure_ne_top _ _)
  have hz : 0< z := half_pos hR
  have hzn : ENNReal.ofReal z < μ U :=
    (ENNReal.ofReal_lt_iff_lt_toReal hz.le (measure_ne_top _ _)).mpr (half_lt_self hR)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (progression_law_tendsto hAP hr hlt hF) hU
  obtain ⟨δ,hδ,H⟩ := class_positive hAP (by positivity : 0<2^k) hr hlt
  refine ⟨z*δ,mul_pos hz hδ,?_⟩
  filter_upwards [H,eventually_lt_of_lt_liminf (hzn.trans_le hport),
    class_nonempty hAP (by positivity : 0<2^k) hr hlt] with X hd hZ hx
  have he := (ENNReal.ofReal_lt_iff_lt_toReal hz.le (measure_ne_top _ _)).mp hZ
  change z < (progressionLaw q r residual X : Measure ℝ).real U at he
  rw [relative_count hx U hU.measurableSet] at he
  have hc : (0:ℝ)<(primeSet (fun n => n%q=r) X).card := by exact_mod_cast card_pos.mpr hx
  calc _ = z*(δ*X.primeCounting) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hd hz.le).trans ((lt_div_iff₀ hc).mp he).le

/-- Both strict excursions of the original integer double sum have positive
lower prime density inside every fixed reduced dyadic class, at any height. -/
theorem original (hAP : ProgressionMangoldt) (b : ℝ) {k r : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r<2^k) :
    PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ b < (S p:ℝ)/p-Real.log p/2) ∧
    PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ (S p:ℝ)/p-Real.log p/2 < -b) := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  change PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ residual p∈Set.Ioi b) ∧
    PositiveLowerPrimeDensity (fun p => p%(2^k)=r ∧ residual p∈Set.Iio (-b))
  exact ⟨dyadic_open_density (U:=Set.Ioi b) hAP hF hr hlt isOpen_Ioi (unbounded_law hAP hF b).1,
    dyadic_open_density (U:=Set.Iio (-b)) hAP hF hr hlt isOpen_Iio (unbounded_law hAP hF (-b)).2⟩
#print axioms unbounded_law
#print axioms dyadic_open_density
#print axioms original
end
end Arxiv.«2501.03234».ThetaUnboundedExcursions
