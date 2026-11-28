import ThetaAlmostPrimeCounts
import ThetaAlmostCrossings
import ThetaAlmostWindowLaw

/-! Frequency of sign changes and the limiting law in almost-all short windows
for the original signed arithmetic sum. -/
namespace Arxiv.«2501.03234».ThetaAlmostPrimeDistribution
open Real Finset Filter MeasureTheory ThetaAlmostPeriodicWindows ThetaWindowApproximation
open ThetaAlmostPrimeCounts ThetaNaturalPrimeMeans ThetaProfiniteUnits ThetaPrimeLaw
open ThetaCharacterPrimeMeans ThetaLocalPrimeCounts ThetaLocalIntervalTests ThetaAlmostWindowLaw
open scoped Topology
noncomputable section

/-- Prime-count inputs at individual lengths, with at most X/log²X bad starts.
They concern only ordinary primes in a fixed residue class. -/
def LowerInput := ∀ β : ℝ, 1/15<β → β<1 → ∃ c : ℝ, 0<c ∧ FixedLower β c

def DistributionInput := ∀ β : ℝ, 1/6<β → β<1 → FixedLimit β

/-- An original-residual interval in a fixed reduced progression has positive
density in every admissible short window outside one set of o(X) starts. -/
theorem excursions (h : LowerInput) (hAP : ProgressionMangoldt)
    {θ : ℝ} (hθ : 1/15<θ) (ht : θ≤1) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ Almost (fun X n => ∀ H : ℕ, Admits θ X H →
      δ*H/log X≤(((sample n H).filter (fun p => p%q=r ∧ |(S p:ℝ)/p-log p/2-y|<d)).card:ℝ)) := by
  let β := (1/15+θ)/2
  obtain ⟨c,hc,hfix⟩ := h β (by dsimp [β];linarith) (by dsimp [β];linarith)
  have hh := ThetaAlmostPrimeCounts.lower (by linarith : 0<θ) (by dsimp [β];linarith : β<θ) hc.le hfix
  obtain ⟨δ,hδ,hh⟩ := ThetaAlmostExcursions.density hh (half_pos hc) hAP hq hr hu y hd
  refine ⟨δ,hδ,?_⟩
  apply mono hh
  filter_upwards with X
  intro n _ hh H hH
  have he : hits q r y d (sample n H)=(sample n H).filter (fun p => p%q=r ∧ |(S p:ℝ)/p-log p/2-y|<d) := by
    classical
    ext p
    constructor
    · intro hs
      obtain ⟨hc,hv⟩ := mem_filter.mp hs
      obtain ⟨hp,hr'⟩ := mem_filter.mp hc
      exact mem_filter.mpr ⟨hp,hr',hv⟩
    · intro hs
      obtain ⟨hp,hr',hv⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hp,hr'⟩,hv⟩
  simpa only [←he] using hh H hH

/-- Both endpoints lie in (X,2X]. In particular, q=1 counts genuine adjacent
ordinary-prime crossings of the signed residual. -/
theorem crossings (h : LowerInput) (hAP : ProgressionMangoldt) {θ : ℝ}
    (hθ : 1/15<θ) (ht : θ<1) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) :
    ∀ᶠ X : ℕ in atTop,(X:ℝ)^(1-θ)/4≤((ThetaCrossingFrequency.starts X q r).card:ℝ) := by
  let β := (1/15+θ)/2
  obtain ⟨c,hc,hfix⟩ := h β (by dsimp [β];linarith) (by dsimp [β];linarith)
  have hh := ThetaAlmostPrimeCounts.lower (by linarith : 0<θ) (by dsimp [β];linarith : β<θ) hc.le hfix
  exact ThetaAlmostCrossings.frequency (by linarith) ht (ThetaAlmostCrossings.windows hh (half_pos hc) hAP hq hr hu)

def Law (θ : ℝ) := (windows θ).NeBot ∧ ∃ F : G →₁[haar] ℝ, Represents residual F ∧
    Tendsto (fun w : Window => ThetaShortResidualLaw.law w.start w.len residual) (windows θ) (𝓝 (haarLaw F)) ∧
    ∀ φ : ℝ → ℝ,Continuous φ → ∀ K : ℝ,0≤K → ∀ k : ℕ,(∀ x, |φ x|≤K*(1+|x|^k)) →
      Tendsto (fun w : Window => ThetaShortResidualLaw.actual w.start w.len (fun p => φ ((S p:ℝ)/p-log p/2)))
        (windows θ) (𝓝 (∫ x, φ x ∂(haarLaw F : Measure ℝ)))

/-- Genuine prime-count-normalized weak convergence and polynomial-growth
tests, including all fixed signed moments, for almost every starting integer. -/
theorem distribution (h : DistributionInput) (hAP : ProgressionMangoldt) {θ : ℝ}
    (hθ : 1/6<θ) (ht : θ≤1) : Law θ := by
  let β := (1/6+θ)/2
  have hβ := h β (by dsimp [β];linarith) (by dsimp [β];linarith)
  have hh := ThetaAlmostPrimeCounts.limit (by linarith : 0<θ) (by dsimp [β];linarith : β<θ) hβ
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  exact ⟨nontrivial ht,F,hF,weak hh hAP hF,fun _ hφ _ hK k hg => polynomial_growth hh hAP hF hφ hK k hg⟩

#print axioms excursions
#print axioms crossings
#print axioms distribution
end
end Arxiv.«2501.03234».ThetaAlmostPrimeDistribution
