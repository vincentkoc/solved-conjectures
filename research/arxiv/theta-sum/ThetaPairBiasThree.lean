import ThetaClassPairMoments
import ThetaCharacterCoefficient

/-! The exact centered pair-product bias modulo three. -/
namespace Arxiv.«2501.03234».ThetaPairBiasThree
open Filter Finset Real MeasureTheory ThetaClassPairLaws ThetaClassPairMoments ThetaPairEmpirical
open ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaConditionalHaar ThetaShortConditionalLaw
open ThetaCharacterPrimeMeans ThetaCharacterCoefficient ThetaDiagonalConstant ThetaAlmostPeriodicWindows
open ThetaIdentityFiber ThetaClassResidualLaws ThetaShortClassMeans ThetaLocalIntervalTests
open ThetaLocalPrimeCounts ThetaShortPrimeInterval ThetaPairTestTruncation
open scoped Topology
noncomputable section

def center (x : ℝ) := x-diagonalConstant
def signedBias (r : ℕ) : ℝ := if r=1 then characterConstant else -characterConstant
def test (z : ℝ×ℝ) := center z.1*center z.2

theorem positive_constant (hAP : ProgressionMangoldt) : 0<characterConstant := by
  obtain ⟨C,hC,hcorr,_⟩ := S_class_prime_means hAP
  rw [←tendsto_nhds_unique hcorr (prime_character_exact hAP)]
  exact lt_of_lt_of_le (by positivity : 0<968/(375*Real.pi^2)) hC

private theorem units {r : ℕ} (hr : r<3) (hu : r.Coprime 3) : r=1 ∨ r=2 := by
  interval_cases r <;> norm_num at *

theorem mean (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {r : ℕ} (hr : r<3) (hu : r.Coprime 3) :
    (∫ x,center x ∂(law F (positive hAP (by decide) hr hu)))=signedBias r := by
  have hg (x : ℝ) : |x|≤1*(1+|x|^1) := by simp
  have hi := ThetaShortConditionalTests.integrable F (positive hAP (by decide) hr hu) continuous_id
    (ThetaResidualMoments.prime_polynomial_growth hAP hF continuous_id hg).1
  change Integrable (fun x : ℝ => x) _ at hi
  have hc := ordinary_tests hAP (by decide : 0<3) hr hu hF continuous_id 1 hg
  obtain ⟨_,_,h1,h2,_⟩ := prime_class_statistics_exact hAP
  rw [show (∫ x,center x ∂(law F (positive hAP (by decide) hr hu)))=
    (∫ x : ℝ,x ∂(law F (positive hAP (by decide) hr hu)))-diagonalConstant by
      simp only [center,integral_sub hi (integrable_const diagonalConstant)]
      simp]
  rcases units hr hu with h|h
  · subst r;have eq := tendsto_nhds_unique hc h1
    change (∫ x : ℝ,x ∂(law F (positive hAP (by decide) hr hu)))=_ at eq
    rw [eq];simp [signedBias]
  · subst r;have eq := tendsto_nhds_unique hc h2
    change (∫ x : ℝ,x ∂(law F (positive hAP (by decide) hr hu)))=_ at eq
    rw [eq];simp [signedBias]

theorem growth (z : ℝ×ℝ) : |test z|≤(1+2*diagonalConstant^2)*(1+|z.1|^2+|z.2|^2) := by
  have h₁ := sq_nonneg (z.1+diagonalConstant)
  have h₂ := sq_nonneg (z.2+diagonalConstant)
  have h₃ := sq_nonneg (|center z.1|-|center z.2|)
  rw [sub_sq,sq_abs,sq_abs] at h₃
  dsimp only [test]
  rw [abs_mul,sq_abs,sq_abs]
  dsimp only [center] at *
  nlinarith only [h₁,h₂,h₃,mul_nonneg (sq_nonneg diagonalConstant) (sq_nonneg z.1),
    mul_nonneg (sq_nonneg diagonalConstant) (sq_nonneg z.2)]

theorem cell_test {θ : ℝ} (hθ : 0<θ) (ht : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {r t : ℕ} (hr : r<3) (hu : r.Coprime 3) (ht₀ : t<3) (hv : t.Coprime 3)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X => ∫ z,test z ∂(empirical (selected 3 r 3 t X (H X)))) atTop (𝓝 (signedBias r*signedBias t)) := by
  have L := tests hθ ht h hAP (by decide) hr hu (by decide) ht₀ hv hF hH
    (show Continuous test by unfold test center;fun_prop) 2 growth
  rw [ProbabilityMeasure.toMeasure_prod,show test=fun z : ℝ×ℝ => center z.1*center z.2 from rfl,
    integral_prod_mul center center,mean hAP hF hr hu,mean hAP hF ht₀ hv] at L
  exact L

#print axioms cell_test
end
end Arxiv.«2501.03234».ThetaPairBiasThree
