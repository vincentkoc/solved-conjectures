import ThetaPairEmpirical
import ThetaWindowTruncation
import Mathlib.Data.Nat.Pairing

/-! A uniform second moment extends the weak law of finite pair samples to
the expectation of a continuous joint test. -/
namespace Arxiv.«2501.03234».ThetaPairTestTruncation
open Filter Finset Real MeasureTheory ThetaPairEmpirical ThetaShortClassMeans ThetaCharacterPrimeMeans
open scoped Topology
noncomputable section

private def index : (Σ _ : ℕ,ℕ) ≃ ℕ := (Equiv.sigmaEquivProd ℕ ℕ).trans Nat.pairEquiv
def observe (p : Σ _ : ℕ,ℕ) : ℝ×ℝ := (residual p.1,residual p.2)

theorem limit {s : ℕ → Finset (Σ _ : ℕ,ℕ)} {μ : ProbabilityMeasure (ℝ×ℝ)}
    {g : ℝ×ℝ → ℝ} (hg : Continuous g) (hi : Integrable g (μ:Measure (ℝ×ℝ)))
    (hw : Tendsto (fun X => empirical (s X)) atTop (𝓝 μ)) {B : ℝ} (hB : 0≤B)
    (hb : ∀ᶠ X : ℕ in atTop,(s X).Nonempty ∧ (∑ z∈s X,(g (observe z))^2)/((s X).card:ℝ)≤B) :
    Tendsto (fun X => ∫ z,g z ∂(empirical (s X))) atTop (𝓝 (∫ z,g z ∂μ)) := by
  let ν := μ.map (f:=g) hg.measurable.aemeasurable
  let c (X : ℕ) := (s X).map index.toEmbedding
  let y (n : ℕ) := g (observe (index.symm n))
  have samples (X : ℕ) (v : ℝ → ℝ) : mean (c X) (fun n => v (y n)) =
      (∑ z∈s X,v (g (observe z)))/((s X).card:ℝ) := by simp [c,y,mean]
  have push {f : ℝ → ℝ} (hf : Measurable f) : (∫ x,f x ∂ν)=∫ z,f (g z) ∂μ := by
    rw [show (ν:Measure ℝ)=(μ:Measure (ℝ×ℝ)).map g from ProbabilityMeasure.toMeasure_map _ _]
    exact integral_map hg.measurable.aemeasurable hf.aestronglyMeasurable
  have integ : Integrable (fun x : ℝ => x) (ν:Measure ℝ) := by
    rw [show (ν:Measure ℝ)=(μ:Measure (ℝ×ℝ)).map g from ProbabilityMeasure.toMeasure_map _ _]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hg.measurable.aemeasurable).mpr hi
  have hh : ∀ᶠ X : ℕ in atTop,(c X).Nonempty ∧ mean (c X) (fun n => (y n)^(1*2))≤B := by
    filter_upwards [hb] with X h
    exact ⟨h.1.map,(samples X (fun x => x^2)).le.trans h.2⟩
  have hw' (ψ : BoundedContinuousFunction ℝ ℝ) :
      Tendsto (fun X => mean (c X) (fun n => ψ (y n))) atTop (𝓝 (∫ x,ψ x ∂ν)) := by
    rw [push ψ.continuous.measurable]
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw (ψ.compContinuous ⟨g,hg⟩)
    apply h.congr'
    filter_upwards [hb] with X hX
    change (∫ z,ψ (g z) ∂(empirical (s X)))=_
    rw [integral_empirical (f:=fun z => ψ (g z)) hX.1 (ψ.continuous.measurable.comp hg.measurable),samples]
    rfl
  have H := ThetaWindowTruncation.limit (φ:=fun x : ℝ => x) continuous_id (K:=1) 1
    (fun x => by simp) integ hB hh hw'
  rw [push (f:=fun x : ℝ => x) measurable_id] at H
  apply H.congr'
  filter_upwards [hb] with X hX
  rw [integral_empirical hX.1 hg.measurable]
  exact samples X (fun x => x)

#print axioms limit
end
end Arxiv.«2501.03234».ThetaPairTestTruncation
