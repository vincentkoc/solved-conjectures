import ThetaNearbyPrimePairs
import ThetaAlmostClassLaws

/-! The scaled two-prime average with independent class restrictions in both coordinates. -/
namespace Arxiv.«2501.03234».ThetaClassPairProducts
open Filter Finset Real MeasureTheory ThetaNearbyPrimePairs ThetaPairComparison ThetaPrimeAnchorTests
open ThetaAlmostPeriodicWindows ThetaAlmostPrimeDistribution ThetaShortClassMeans ThetaConditionalHaar
open ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaIdentityFiber ThetaCharacterPrimeMeans
open ThetaShortConditionalLaw
open scoped Topology BoundedContinuousFunction
noncomputable section

def mark (q r : ℕ) (u : ℝ →ᵇ ℝ) (p : ℕ) := selectClass r q p*u (residual p)

theorem bound (q r : ℕ) (u : ℝ →ᵇ ℝ) (p : ℕ) : |mark q r u p|≤‖u‖ := by
  dsimp only [mark,selectClass]
  split_ifs
  · rw [one_mul,←Real.norm_eq_abs];exact u.norm_coe_le_norm _
  · simpa using norm_nonneg u

private theorem growth (u : ℝ →ᵇ ℝ) (x : ℝ) : |u x|≤‖u‖*(1+|x|^0) := by
  have hx := u.norm_coe_le_norm x
  rw [Real.norm_eq_abs] at hx
  rw [pow_zero];linarith only [hx,norm_nonneg u]

theorem mean_limit (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) (u : ℝ →ᵇ ℝ) :
    Tendsto (primeMean (mark q r u)) atTop (𝓝 (1/(q.totient:ℝ)*(∫ x,u x ∂(law F (positive hAP hq hr hu))))) :=
  ThetaShortClassMeans.factor hq hr hu hAP (ThetaClassResidualLaws.ordinary_tests hAP hq hr hu hF u.continuous 0 (growth u))

theorem approximable (hAP : ProgressionMangoldt) {q : ℕ} (hq : 0<q) (r : ℕ)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) (u : ℝ →ᵇ ℝ) : Approximable (mark q r u) := by
  have ha := ThetaPrimeTestApproximation.original hAP hF u.continuous (norm_nonneg u) 0 (growth u)
  obtain ⟨Y,hY⟩ := exists_haar_representative hAP ha
  obtain ⟨Z,hZ,_⟩ := masked hY hq r
  intro ε he
  obtain ⟨T,b,hb,hh,_⟩ := hZ ε he
  exact ⟨T,b,hb,hh⟩

theorem product_limit {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r s t : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (hs : 0<s) (ht₀ : t<s) (hv : t.Coprime s)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) (u v : ℝ →ᵇ ℝ) {H : ℕ → ℕ}
    (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X => scaled X (H X) (mark q r u) (mark s t v)) atTop
      (𝓝 ((1/(q.totient:ℝ)*(∫ x,u x ∂(law F (positive hAP hq hr hu))))*
        (1/(s.totient:ℝ)*(∫ x,v x ∂(law F (positive hAP hs ht₀ hv)))))) := by
  apply product ht hAP (B:=‖u‖+1) (D:=‖v‖) (by positivity) (fun p => (bound q r u p).trans (by linarith))
    (norm_nonneg v) (bound s t v) (mean_limit hAP hq hr hu hF u) _ hH
  exact fun _ he => limit ht ht' h hAP (ThetaPrimeAnchorTransfer.bounded (bound s t v))
    (approximable hAP hs t hF v) (mean_limit hAP hs ht₀ hv hF v) he

#print axioms product_limit
end
end Arxiv.«2501.03234».ThetaClassPairProducts
