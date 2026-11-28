import ThetaDoubleExponentialTails
import ThetaLargeLawTails

/-! Matching double-exponential order for each side of the limiting law. -/
namespace Arxiv.«2501.03234».ThetaDoubleExponentialLaw
open Real Filter Finset MeasureTheory ThetaDoubleExponentialTails ThetaCharacterPrimeMeans
open ThetaDiagonalConstant ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaPrimeDensity
open scoped Topology
noncomputable section

def outside (b : ℝ) := {x : ℝ | b < |x-diagonalConstant|}

theorem two_sided (hAP : ProgressionMangoldt) : ∃ c : ℝ, 0<c ∧ ∀ᶠ b : ℝ in atTop,
    ∀ F : G →₁[haar] ℝ, Represents residual F →
      let μ := (haarLaw F : Measure ℝ)
      let lower := ENNReal.ofReal (exp (-exp (32*π*sqrt b)))
      lower ≤ μ (Set.Ioi (diagonalConstant+b)) ∧ lower ≤ μ (Set.Iio (diagonalConstant-b)) ∧
        μ (outside b) ≤ ENNReal.ofReal (exp (-exp (c*sqrt b))) := by
  obtain ⟨c,hc,H⟩ := original_prime hAP
  refine ⟨c,hc,?_⟩
  filter_upwards [H,ThetaLargeLawTails.tails hAP] with b hX hlow
  intro F hF
  refine ⟨(hlow F hF).1,(hlow F hF).2,?_⟩
  have hopen : IsOpen (outside b) := isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto (empirical_tendsto hAP hF) hopen).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hX,eventually_ge_atTop 2] with X hX htwo
  rw [← ENNReal.ofReal_toReal (measure_ne_top (empirical residual X : Measure ℝ) _)]
  apply ENNReal.ofReal_le_ofReal
  change (empirical residual X : Measure ℝ).real (outside b)≤_
  rw [empirical_real_set htwo residual hopen.measurableSet]
  exact hX

#print axioms two_sided
end
end Arxiv.«2501.03234».ThetaDoubleExponentialLaw
