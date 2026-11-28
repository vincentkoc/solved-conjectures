import ThetaDoubleExponentialLaw
import ThetaUnboundedExcursions

/-! Double-exponential lower and upper excursion counts inside fixed dyadic prime classes. -/
namespace Arxiv.«2501.03234».ThetaDyadicTailCounts
open Real Filter Finset MeasureTheory ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeDensity
open ThetaDiagonalConstant ThetaPrimeLaw ThetaProfiniteUnits ThetaDyadicLaw ThetaUnboundedExcursions
open scoped Topology
noncomputable section

/-- The denominator counts primes in the same class as the numerator. -/
def fraction (q r X : ℕ) (P : ℕ → Prop) : ℝ := by
  classical
  exact ((primeSet (fun p => p%q=r ∧ P p) X).card:ℝ)/(primeSet (fun p => p%q=r) X).card

private theorem lower_open (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) {k r : ℕ} (hr : r.Coprime (2^k)) (hlt : r<2^k)
    {U : Set ℝ} (hU : IsOpen U) {l : ℝ} (hl : 0<l)
    (hμ : ENNReal.ofReal l≤(haarLaw F : Measure ℝ) U) :
    ∀ᶠ X : ℕ in atTop, l/2≤fraction (2^k) r X (fun p => residual p∈U) := by
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (progression_law_tendsto hAP hr hlt hF) hU
  have hstrict := (ENNReal.ofReal_lt_ofReal_iff hl).mpr (half_lt_self hl)
  filter_upwards [eventually_lt_of_lt_liminf (hstrict.trans_le (hμ.trans hlim)),
    class_nonempty hAP (by positivity : 0<2^k) hr hlt] with X hX hx
  have hh := (ENNReal.ofReal_lt_iff_lt_toReal (half_pos hl).le (measure_ne_top _ _)).mp hX
  change l/2 < (progressionLaw (2^k) r residual X : Measure ℝ).real U at hh
  rw [relative_count hx U hU.measurableSet] at hh
  exact hh.le

private theorem upper_closed (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) {k r : ℕ} (hr : r.Coprime (2^k)) (hlt : r<2^k)
    {K : Set ℝ} (hK : IsClosed K) {u : ℝ} (hu : 0<u)
    (hμ : (haarLaw F : Measure ℝ) K≤ENNReal.ofReal u) :
    ∀ᶠ X : ℕ in atTop, fraction (2^k) r X (fun p => residual p∈K)≤2*u := by
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (progression_law_tendsto hAP hr hlt hF) hK
  have hstrict := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0<2*u)).mpr (show u<2*u by linarith)
  filter_upwards [eventually_lt_of_limsup_lt ((hlim.trans hμ).trans_lt hstrict),
    class_nonempty hAP (by positivity : 0<2^k) hr hlt] with X hX hx
  have hh := ENNReal.toReal_lt_of_lt_ofReal hX
  change (progressionLaw (2^k) r residual X : Measure ℝ).real K <2*u at hh
  rw [relative_count hx K hK.measurableSet] at hh
  exact hh.le

/-- Both signs occur with double-exponential frequency relative to their own prime
class. The upper estimate counts both tails together, including equality at b. -/
theorem original (hAP : ProgressionMangoldt) : ∃ c : ℝ, 0<c ∧
    ∀ᶠ b : ℝ in atTop, ∀ k r : ℕ, r.Coprime (2^k) → r<2^k →
      ∀ᶠ X : ℕ in atTop,
        let l := exp (-exp (32*π*sqrt b))/2
        let R := fun p : ℕ => (S p:ℝ)/p-log p/2-diagonalConstant
        l≤fraction (2^k) r X (fun p => b<R p) ∧
        l≤fraction (2^k) r X (fun p => R p< -b) ∧
        fraction (2^k) r X (fun p => b≤|R p|)≤2*exp (-exp (c*sqrt b)) := by
  obtain ⟨a,ha,H⟩ := ThetaDoubleExponentialLaw.two_sided hAP
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  have hscale : Tendsto (fun b : ℝ => b/4) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  refine ⟨a/2,half_pos ha,?_⟩
  filter_upwards [H,hscale.eventually H,eventually_gt_atTop (0:ℝ)] with b hb hsmall hpos
  intro k r hr hlt
  let K := {x : ℝ | b≤|x-diagonalConstant|}
  have hK : IsClosed K := isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)
  have hsub : K⊆ThetaDoubleExponentialLaw.outside (b/4) := by
    intro x hx
    change b/4 < |x-diagonalConstant|
    change b≤|x-diagonalConstant| at hx
    linarith
  obtain ⟨hplus,hminus,_⟩ := hb F hF
  have hup := (measure_mono hsub).trans (hsmall F hF).2.2
  have hs : a*sqrt (b/4)=a/2*sqrt b := by rw [sqrt_div hpos.le];norm_num;ring
  rw [hs] at hup
  filter_upwards [lower_open hAP hF hr hlt isOpen_Ioi (exp_pos _) hplus,
    lower_open hAP hF hr hlt isOpen_Iio (exp_pos _) hminus,
    upper_closed hAP hF hr hlt hK (exp_pos _) hup] with X hp hm hu
  refine ⟨?_,?_,hu⟩
  · convert hp using 2
    ext p
    change (b<residual p-diagonalConstant) ↔ (diagonalConstant+b<residual p)
    constructor <;> intro h <;> linarith
  · convert hm using 2
    ext p
    change (residual p-diagonalConstant< -b) ↔ (residual p<diagonalConstant-b)
    constructor <;> intro h <;> linarith

#print axioms original
end
end Arxiv.«2501.03234».ThetaDyadicTailCounts
