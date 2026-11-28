import ThetaShortConditionalLaw
import ThetaWindowTruncation

/-! Conditional polynomial-growth tests remain valid on every eligible
short interval in every fixed reduced progression. -/
namespace Arxiv.«2501.03234».ThetaShortConditionalTests
open Filter Finset Real MeasureTheory ProbabilityTheory ThetaConditionalHaar ThetaShortClassMeans
open ThetaProfiniteUnits ThetaPrimeLaw ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open ThetaCalibratedCone ThetaLocalPrimeCounts ThetaShortConditionalLaw
open scoped Topology
noncomputable section

theorem integrable (F : G →₁[haar] ℝ) {q r : ℕ} (hc : haar (fibre q r)≠0) {φ : ℝ → ℝ}
    (hp : Continuous φ) (hi : Integrable φ (haarLaw F : Measure ℝ)) :
    Integrable φ (law F hc : Measure ℝ) := by
  have hm := (Lp.aestronglyMeasurable F).aemeasurable
  have hFc := (integrable_map_measure hp.aestronglyMeasurable hm).mp hi
  apply (integrable_map_measure hp.aestronglyMeasurable
    (hm.mono_ac (cond_absolutelyContinuous (μ:=haar) (s:=fibre q r)))).mpr
  exact hFc.restrict.smul_measure (ENNReal.inv_ne_top.mpr hc)

theorem moment_bound {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {H : ℕ → ℕ} (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X) (k : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ X : ℕ in atTop,mean (window q r X (H X)) (fun p => (residual p)^(k*2))≤B := by
  let I := ∫ x : ℝ,x^(k*2) ∂(haarLaw F)
  let b := |I|+1
  have hb : 0<b := by dsimp [b];positivity
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hM := (ThetaShortResidualLaw.moments he h48 hk hθ hθ₁ h hAP hF hh (k*2)).eventually_le_const
    (show I<b by dsimp [b];linarith only [le_abs_self I])
  refine ⟨4*q.totient*b,by positivity,?_⟩
  filter_upwards [hM,hh,ThetaLocalMomentBudgets.count h,ThetaShortResidualSupport.class_count h hq hr hu,
    ThetaWindowClassMeasure.nonempty h hAP hq hr hu hh] with X hM hx hs hc hp
  let s := sample X (H X)
  let z := window q r X (H X)
  have hsub : z⊆s := filter_subset ..
  have hc' := (div_le_iff₀ (by positivity : 0<2*(q.totient:ℝ))).mp (hc _ hx.1 hx.2)
  have hs' := (hs _ hx.1 hx.2).2
  change mass X (H X)≤(z.card:ℝ)*(2*q.totient) at hc'
  change (s.card:ℝ)≤2*mass X (H X) at hs'
  have hh := dominated (s:=z) (z:=s) hp hsub (f:=fun p => (residual p)^(k*2))
    (fun p => by rw [pow_mul];exact sq_nonneg _) (D:=4*q.totient) (by linarith only [hc',hs']) hb.le hM
  simpa only [mul_comm b] using hh

theorem original {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {H : ℕ → ℕ} (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X)
    {φ : ℝ → ℝ} (hp : Continuous φ) {K : ℝ} (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k)) :
    Tendsto (fun X => mean (window q r X (H X)) (fun p => φ ((S p:ℝ)/p-log p/2))) atTop
      (𝓝 (∫ x,φ x ∂(law F (positive hAP hq hr hu)))) := by
  obtain ⟨B,hB,hm⟩ := moment_bound he h48 hk hθ hθ₁ h hAP hq hr hu hF hh k
  have hz := ThetaWindowClassMeasure.nonempty h hAP hq hr hu hh
  have hl := ThetaShortConditionalLaw.weak he h48 hk hθ hθ₁ h hAP hq hr hu hF hh
  apply ThetaWindowTruncation.limit hp k hg (integrable F _ hp (ThetaResidualMoments.prime_polynomial_growth hAP hF hp hg).1)
    hB (hz.and hm)
  intro ψ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hl ψ).congr'
    (hz.mono (fun X hx => ThetaWindowClassMeasure.integral_eq hx ψ.continuous.measurable))

#print axioms original
end
end Arxiv.«2501.03234».ThetaShortConditionalTests
