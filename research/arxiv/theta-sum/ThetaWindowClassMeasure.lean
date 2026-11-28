import ThetaShortClassMeans

/-! The empirical probability measure on a finite prime sample and the
nonemptiness of each fixed reduced class in every eligible short window. -/
namespace Arxiv.«2501.03234».ThetaWindowClassMeasure
open Real Filter Finset MeasureTheory ThetaPrimeLaw ThetaProfiniteUnits ThetaCharacterPrimeMeans
open ThetaLocalDyadicReference ThetaNaturalPrimeMeans ThetaShortClassMeans ThetaDyadicLaw
open ThetaLocalPrimeCounts ThetaCalibratedCone ThetaLocalIntervalTests ThetaIdentityFiber
open scoped Topology NNReal
noncomputable section

private def support (s : Finset ℕ) : Finset ℕ := if s.Nonempty then s else {2}
private instance (s : Finset ℕ) : Nonempty ↥(support s) := by
  classical
  unfold support
  split_ifs with h
  · exact h.to_subtype
  · exact ⟨⟨2,by simp⟩⟩

private def uniform (s : Finset ℕ) : ProbabilityMeasure ↥(support s) :=
  ⟨(PMF.uniformOfFintype _).toMeasure,inferInstance⟩

def law (s : Finset ℕ) : ProbabilityMeasure ℝ :=
  (uniform s).map (f:=fun p => residual p.val) (measurable_of_countable _).aemeasurable

theorem integral_eq {s : Finset ℕ} (hs : s.Nonempty) {φ : ℝ → ℝ} (hc : Measurable φ) :
    (∫ x,φ x ∂(law s))=mean s (fun p => φ (residual p)) := by
  rw [law,ProbabilityMeasure.toMeasure_map,integral_map (measurable_of_countable _).aemeasurable hc.aestronglyMeasurable]
  change (∫ p : ↥(support s), φ (residual p.val) ∂(PMF.uniformOfFintype _).toMeasure)=_
  rw [PMF.integral_eq_sum]
  have hh : (∑ p : ↥(support s), φ (residual p.val))=∑ p∈support s,φ (residual p) :=
    Finset.sum_attach (support s) (fun p => φ (residual p))
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,
    ←mul_sum,hh,Fintype.card_coe,mean,div_eq_inv_mul]
  rw [show support s=s from if_pos hs]

theorem nonempty {θ : ℝ} (h : Ordinary θ) (hAP : ProgressionMangoldt) {q r : ℕ}
    (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X) :
    ∀ᶠ X : ℕ in atTop,(window q r X (H X)).Nonempty := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  filter_upwards [(denominator h hAP hq hr hu hh).eventually_const_lt (by positivity : 0<1/(q.totient:ℝ))] with X hx
  by_contra he
  simp [not_nonempty_iff_eq_empty.mp he] at hx

#print axioms integral_eq
#print axioms nonempty
end
end Arxiv.«2501.03234».ThetaWindowClassMeasure
