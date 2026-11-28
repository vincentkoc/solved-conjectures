import ThetaPairEmpirical
import ThetaProductTests

/-! The joint residual law for an unweighted directed pair with first prime in
(X,2X] and second prime at distance at most H. -/
namespace Arxiv.«2501.03234».ThetaNearbyResidualLaw
open Real Filter MeasureTheory ThetaAlmostPeriodicWindows ThetaAlmostPrimeDistribution
open ThetaNaturalPrimeMeans ThetaPrimeStartDensity ThetaProfiniteUnits ThetaPrimeLaw
open ThetaCharacterPrimeMeans ThetaNearbyPrimePairs
open scoped Topology
noncomputable section

theorem weak {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ}
    (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X => ThetaPairEmpirical.law X (H X)) atTop (𝓝 ((haarLaw F).prod (haarLaw F))) := by
  apply ThetaProductTests.weak
  intro u v
  have hmass := pair_mass ht ht' h hAP hH
  have hh := averages ht ht' h hAP hF u.continuous v.continuous (norm_nonneg u)
    (fun x => (Real.norm_eq_abs _).symm.le.trans (u.norm_coe_le_norm x)) (norm_nonneg v)
    (fun x => (Real.norm_eq_abs _).symm.le.trans (v.norm_coe_le_norm x)) hH
  have he : ThetaProductTests.val ((haarLaw F).prod (haarLaw F)) u v=
      (∫ x, u x ∂(haarLaw F:Measure ℝ))*(∫ x, v x ∂(haarLaw F:Measure ℝ)) :=
    integral_prod_mul u v
  rw [he]
  apply hh.congr'
  filter_upwards [hmass.eventually_const_lt (by norm_num : (0:ℝ)<1)] with X hx
  have hc : 0<count X (H X) := by
    by_contra! hz
    rw [Nat.le_zero.mp hz] at hx
    simp at hx
  exact (ThetaPairEmpirical.integral_eq hc u.continuous.measurable v.continuous.measurable).symm

/-- One Haar law works for every admissible length schedule. Only ordinary
per-length progression counts are needed in the almost-all window input. -/
theorem distribution (h : DistributionInput) (hAP : ProgressionMangoldt) {θ : ℝ}
    (hθ : 1/6<θ) (ht : θ≤1) :
    ∃ F : G →₁[haar] ℝ,Represents residual F ∧ ∀ H : ℕ → ℕ,
      (∀ᶠ X : ℕ in atTop,Admits θ X (H X)) →
      Tendsto (fun X => ThetaPairEmpirical.law X (H X)) atTop (𝓝 ((haarLaw F).prod (haarLaw F))) ∧
      Tendsto (fun X : ℕ => (log X/X*(log X/H X))*(count X (H X):ℝ)) atTop (𝓝 1) := by
  let β := (1/6+θ)/2
  have hβ := h β (by dsimp [β];linarith) (by dsimp [β];linarith)
  have h₀ : 0<θ := by linarith
  have hh := ThetaAlmostPrimeCounts.limit h₀ (by dsimp [β];linarith : β<θ) hβ
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  exact ⟨F,hF,fun _ hH => ⟨weak h₀ ht hh hAP hF hH,pair_mass h₀ ht hh hAP hH⟩⟩

#print axioms distribution
end
end Arxiv.«2501.03234».ThetaNearbyResidualLaw
