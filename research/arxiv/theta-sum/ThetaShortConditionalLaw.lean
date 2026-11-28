import ThetaConditionalHaar
import ThetaWindowClassMeasure

/-! All reduced residue classes have a short-window weak limit obtained by
restricting the same Haar representative to their corresponding fibre. -/
namespace Arxiv.«2501.03234».ThetaShortConditionalLaw
open Filter Finset MeasureTheory ProbabilityTheory ThetaConditionalHaar ThetaShortClassMeans
open ThetaProfiniteUnits ThetaPrimeLaw ThetaCharacterPrimeMeans ThetaIdentityFiber ThetaNaturalPrimeMeans
open ThetaWindowClassMeasure ThetaCalibratedCone ThetaLocalPrimeCounts
open scoped Topology NNReal
noncomputable section

def law (F : G →₁[haar] ℝ) {q r : ℕ} (hc : haar (fibre q r)≠0) : ProbabilityMeasure ℝ :=
  let μ : ProbabilityMeasure G := ⟨cond haar (fibre q r),cond_isProbabilityMeasure hc⟩
  μ.map (f:=fun x => F x) ((Lp.aestronglyMeasurable F).aemeasurable.mono_ac cond_absolutelyContinuous)

theorem positive (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) :
    haar (fibre q r)≠0 := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hh := mass hAP hq hr hu
  intro hz
  rw [measureReal_def,hz,ENNReal.toReal_zero] at hh
  linarith only [hh,one_div_pos.mpr hφ]

theorem scaled_integral (F : G →₁[haar] ℝ) {q r : ℕ} (hc : haar (fibre q r)≠0) {φ : ℝ → ℝ}
    (hφ : Continuous φ) : haar.real (fibre q r)*(∫ x,φ x ∂(law F hc))=∫ x in fibre q r,φ (F x) ∂haar := by
  have hmeas := (Lp.aestronglyMeasurable F).aemeasurable.mono_ac
    (cond_absolutelyContinuous (μ:=haar) (s:=fibre q r))
  change _*(∫ x,φ x ∂(Measure.map (fun x => F x) (cond haar (fibre q r))))=_
  rw [integral_map hmeas hφ.aestronglyMeasurable,ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  have hp : haar.real (fibre q r)≠0 := ENNReal.toReal_ne_zero.mpr ⟨hc,measure_ne_top _ _⟩
  change haar.real (fibre q r)*((haar.real (fibre q r))⁻¹*_)=_
  rw [←mul_assoc,mul_inv_cancel₀ hp,one_mul]

theorem weighted (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) {F : G →₁[haar] ℝ}
    (hF : Represents residual F) {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) :
    Tendsto (primeMean (fun p => selectClass r q p*φ (residual p))) atTop
      (𝓝 (∫ x in fibre q r,φ (F x) ∂haar)) := by
  obtain ⟨Y,hY,hye⟩ := composed hF hp
  obtain ⟨Z,hZ,hze⟩ := masked hY hq r
  have h := prime_mean_lipschitz hAP hZ LipschitzWith.id
  change Tendsto _ atTop (𝓝 (∫ x,Z x ∂haar)) at h
  have he : (∫ x,Z x ∂haar)=∫ x in fibre q r,φ (F x) ∂haar := by
    rw [←integral_indicator (measurable q r)]
    apply integral_congr_ae
    filter_upwards [hye,hze] with x hy hz
    change Z x=(fibre q r).indicator (fun y => φ (F y)) x
    rw [show Z x=(fibre q r).indicator (fun y => Y y) x from hz]
    by_cases hx : x∈fibre q r <;> simp [hx,hy]
  rwa [he] at h

theorem short_lipschitz {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {H : ℕ → ℕ} (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) :
    Tendsto (fun X => mean (window q r X (H X)) (fun p => φ (residual p))) atTop
      (𝓝 (∫ x,φ x ∂(law F (positive hAP hq hr hu)))) := by
  have hb (p : ℕ) : |selectClass r q p|≤1 := by dsimp [selectClass];split_ifs <;> norm_num
  obtain ⟨a,ha,H'⟩ := ThetaLocalWeightedLimits.common he h48 hk hθ hθ₁ h hAP hq (selectClass_mod r q) hb hp
  have eq := tendsto_nhds_unique ha (weighted (r:=r) hAP hq hF hp)
  have ei := scaled_integral F (positive hAP hq hr hu) hp.continuous
  rw [mass hAP hq hr hu] at ei
  apply normalize h hAP hq hr hu hh
  rw [ei,←eq]
  apply Metric.tendsto_nhds.mpr;intro ε hε
  filter_upwards [H' ε hε,hh] with X h₁ h₂
  exact h₁ _ h₂.1 h₂.2

theorem weak {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {H : ℕ → ℕ} (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X) :
    Tendsto (fun X => ThetaWindowClassMeasure.law (window q r X (H X))) atTop (𝓝 (law F (positive hAP hq hr hu))) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ _ ⟨K,hp⟩
  exact (short_lipschitz he h48 hk hθ hθ₁ h hAP hq hr hu hF hh hp).congr'
    ((nonempty h hAP hq hr hu hh).mono (fun X hx => (ThetaWindowClassMeasure.integral_eq hx hp.continuous.measurable).symm))

#print axioms weak
#print axioms weighted
end
end Arxiv.«2501.03234».ThetaShortConditionalLaw
