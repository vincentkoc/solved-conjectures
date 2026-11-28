import ThetaNearbyPrimePairs
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! The unweighted empirical probability measure on the two actual residuals
of each directed prime pair. -/
namespace Arxiv.«2501.03234».ThetaPairEmpirical
open Real Filter Finset MeasureTheory ThetaLocalPrimeCounts ThetaCharacterPrimeMeans ThetaNearbyPrimePairs
open scoped Topology
noncomputable section

def pairs (X H : ℕ) := (sample X X).sigma (fun p => sample p H)
theorem size (X H : ℕ) : (pairs X H).card=count X H := card_sigma ..

private def support (s : Finset (Σ _ : ℕ, ℕ)) : Finset (Σ _ : ℕ, ℕ) := by
  classical exact if s.Nonempty then s else {⟨2,3⟩}
private instance (s : Finset (Σ _ : ℕ, ℕ)) : Nonempty ↥(support s) := by
  classical
  dsimp only [support]
  split_ifs with h
  · exact h.to_subtype
  · exact ⟨⟨_,mem_singleton_self _⟩⟩
private instance (s : Finset (Σ _ : ℕ, ℕ)) : MeasurableSpace ↥(support s) := ⊤
private instance (s : Finset (Σ _ : ℕ, ℕ)) : MeasurableSingletonClass ↥(support s) := ⟨fun _ => trivial⟩
private def uniform (s : Finset (Σ _ : ℕ, ℕ)) : ProbabilityMeasure ↥(support s) :=
  ⟨(PMF.uniformOfFintype _).toMeasure,inferInstance⟩

/-- The equal-weight residual law of an arbitrary finite sample of prime pairs. -/
def empirical (s : Finset (Σ _ : ℕ, ℕ)) : ProbabilityMeasure (ℝ×ℝ) :=
  (uniform s).map (f:=fun p => (residual p.val.1,residual p.val.2)) (measurable_of_countable _).aemeasurable

def law (X H : ℕ) := empirical (pairs X H)

theorem integral_empirical {s : Finset (Σ _ : ℕ, ℕ)} (hn : s.Nonempty)
    {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    (∫ z,f z ∂(empirical s : Measure (ℝ×ℝ))) =
      (∑ p∈s,f (residual p.1,residual p.2))/s.card := by
  rw [empirical,ProbabilityMeasure.toMeasure_map,integral_map (f:=f) (measurable_of_countable _).aemeasurable
    hf.aestronglyMeasurable]
  let u (p : Σ _ : ℕ,ℕ) := f (residual p.1,residual p.2)
  change (∫ p : ↥(support s),u p.val ∂(PMF.uniformOfFintype _).toMeasure)=_
  rw [PMF.integral_eq_sum]
  have hs : (∑ p : ↥(support s),u p.val)=∑ p∈support s,u p := Finset.sum_attach ..
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,←mul_sum,
    hs,Fintype.card_coe,div_eq_inv_mul]
  rw [show support s=s from if_pos hn]

theorem integral_eq {X H : ℕ} (h : 0<count X H) {φ ψ : ℝ → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫ z : ℝ×ℝ, φ z.1*ψ z.2 ∂(law X H : Measure (ℝ×ℝ))) = actual X H (fun p => φ (residual p)) (fun p => ψ (residual p)) := by
  have hn := card_pos.mp (show 0<(pairs X H).card by rwa [size])
  rw [law,integral_empirical (f:=fun z : ℝ×ℝ => φ z.1*ψ z.2) hn ((hφ.comp measurable_fst).mul (hψ.comp measurable_snd)),size,actual]
  congr 1
  exact sum_sigma ..

#print axioms integral_eq
end
end Arxiv.«2501.03234».ThetaPairEmpirical
