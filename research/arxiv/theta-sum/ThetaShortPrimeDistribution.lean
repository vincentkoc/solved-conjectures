import ThetaShortResidualSupport
import ThetaWeilShortIntervals

/-! Short-window concentration, natural-prime weak convergence, and moment
limits for the original signed integer double sum. -/
namespace Arxiv.«2501.03234».ThetaShortPrimeDistribution
open Real Filter MeasureTheory ThetaLocalPrimeCounts ThetaProfiniteUnits ThetaPrimeLaw
open ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans ThetaCalibratedCone ThetaLocalIntervalTests
open scoped Topology
noncomputable section

def Statement (θ : ℝ) : Prop :=
  (∀ {q r : ℕ}, 0<q → r<q → r.Coprime q → ∀ y : ℝ, ∀ {d : ℝ}, 0<d →
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      δ*H/log X≤((hits q r y d (sample X H)).card:ℝ)) ∧
  ∃ F : G →₁[haar] ℝ, Represents residual F ∧ ∀ H : ℕ → ℕ,
    (∀ᶠ X : ℕ in atTop, H X≤X ∧ (X:ℝ)^θ≤H X) →
    Tendsto (fun X => ThetaShortResidualLaw.law X (H X) residual) atTop (𝓝 (haarLaw F)) ∧
    ∀ k : ℕ, Tendsto (fun X => ThetaShortResidualLaw.actual X (H X)
      (fun p => ((S p:ℝ)/p-log p/2)^k)) atTop (𝓝 (∫ x, x^k ∂(haarLaw F : Measure ℝ)))

theorem original {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt) : Statement θ := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  refine ⟨?_,F,hF,?_⟩
  · intro q r hq hr hc y d hd
    exact ThetaShortResidualSupport.density he h48 hk hθ hθ₁ h hAP hq hr hc y hd
  · intro H hh
    exact ⟨ThetaShortResidualLaw.weak he h48 hk hθ hθ₁ h hAP hF hh,
      ThetaShortResidualLaw.moments he h48 hk hθ hθ₁ h hAP hF hh⟩

theorem elementary {θ : ℝ} (hθ : 3/4<θ) (hθ₁ : θ≤1) (h : Ordinary θ)
    (hAP : ProgressionMangoldt) : Statement θ :=
  original (e:=48) (by decide) (le_refl 48) elementary_kernel (by norm_num;linarith) hθ₁ h hAP

theorem weil {θ : ℝ} (hθ : 1/2<θ) (hθ₁ : θ≤1) (hw : ThetaWeilShortIntervals.Weil)
    (h : Ordinary θ) (hAP : ProgressionMangoldt) : Statement θ :=
  original (e:=32) (le_refl 32) (by decide) (ThetaWeilShortIntervals.kernel hw) (by norm_num;linarith) hθ₁ h hAP

#print axioms original
#print axioms elementary
#print axioms weil
end
end Arxiv.«2501.03234».ThetaShortPrimeDistribution
