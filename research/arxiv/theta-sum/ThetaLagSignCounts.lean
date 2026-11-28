import ThetaLagSignThreshold
import ThetaDistinctPrimeQuadruples

/-! At a fixed continuity threshold the upper and lower marks have the same
prime density, yet agree on more nearby prime pairs than disagree. -/
namespace Arxiv.«2501.03234».ThetaLagSignCounts
open Real Filter Finset MeasureTheory ThetaAsymmetricTails ThetaPrimeLaw ThetaPrimeDensity
open ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans ThetaPeriodMeans ThetaDiagonalConstant
open ThetaLogarithmicLags ThetaPrimeLagBounds ThetaDistinctPrimeQuadruples
open scoped Topology
noncomputable section

def sameTail (t x y : ℝ) := (t<x ∧ t<y) ∨ (x< -t ∧ y< -t)
def oppositeTail (t x y : ℝ) := (t<x ∧ y< -t) ∨ (x< -t ∧ t<y)

def pairCount (X h : ℕ) (f : ℕ → ℝ) (P : ℝ → ℝ → Prop) : ℕ := by
  classical
  exact ((pairs X h).filter (fun p => P (f p) (f (p+h)))).card

theorem marked (X h : ℕ) (t : ℝ) (f : ℕ → ℝ) :
    corr X h (fun p => mark t (f p))=
      (pairCount X h f (sameTail t):ℝ)-pairCount X h f (oppositeTail t) := by
  classical
  have point (x y : ℝ) : mark t x*mark t y=(if sameTail t x y then 1 else 0)-
      (if oppositeTail t x y then 1 else 0) := by
    by_cases a : t<x <;> by_cases b : x< -t <;> by_cases c : t<y <;> by_cases d : y< -t <;>
      simp [mark,sameTail,oppositeTail,a,b,c,d]
  change (∑ p∈pairs X h,_) = _
  simp only [point,sum_sub_distrib,sum_boole,pairCount]

theorem balanced {μ : ProbabilityMeasure ℝ} (hμ : reflectedLaw diagonalConstant μ=μ)
    (h : Tendsto (empirical residual) atTop (𝓝 μ)) :
    ∀ᵐ t : ℝ,Tendsto (primeMean (fun p => mark t (residual p-diagonalConstant))) atTop (𝓝 0) := by
  let B := diagonalConstant
  let ν := (μ:Measure ℝ)
  filter_upwards [atom ν (fun x => x-B) (by fun_prop),atom ν (fun x => B-x) (by fun_prop)] with t ha hb
  have ha' : ν {B+t}=0 := by
    rw [←ha];congr 1;ext x;simp only [Set.mem_singleton_iff,Set.mem_ofPred_eq];constructor <;> intro hh <;> linarith
  have hb' : ν {B-t}=0 := by
    rw [←hb];congr 1;ext x;simp only [Set.mem_singleton_iff,Set.mem_ofPred_eq];constructor <;> intro hh <;> linarith
  have heq : ν (Set.Ioi (B+t))=ν (Set.Iio (B-t)) := by
    calc
      _ = (reflectedLaw B μ : Measure ℝ) (Set.Ioi (B+t)) := by rw [hμ]
      _ = ν ((fun x : ℝ => 2*B-x) ⁻¹' Set.Ioi (B+t)) := by
        apply Measure.map_apply (by fun_prop) measurableSet_Ioi
      _ = _ := by congr 1;ext x;simp only [Set.mem_preimage,Set.mem_Ioi,Set.mem_Iio];constructor <;> intro hh <;> linarith
  have H := (count_limit h measurableSet_Ioi (by simpa only [frontier_Ioi] using ha')).sub
    (count_limit h measurableSet_Iio (by simpa only [frontier_Iio] using hb'))
  have ee : (μ:Measure ℝ).real (Set.Ioi (B+t))=(μ:Measure ℝ).real (Set.Iio (B-t)) := congrArg ENNReal.toReal heq
  rw [ee,sub_self] at H
  apply H.congr (fun X => ?_)
  have a (x : ℝ) : t<x-diagonalConstant ↔ B+t<x := by dsimp [B];constructor <;> intro hh <;> linarith
  have b (x : ℝ) : x-diagonalConstant< -t ↔ x<B-t := by dsimp [B];constructor <;> intro hh <;> linarith
  simp only [mark,a,b,primeMean,sum_sub_distrib,sum_boole,primeSet,Set.mem_Ioi,Set.mem_Iio,sub_div]

theorem balanced_scales (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ q : ℕ,m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ t c : ℝ,0<t ∧ 0<c ∧
      Tendsto (primeMean (fun p => mark t (residual p-diagonalConstant))) atTop (𝓝 0) ∧
      Scales q c (fun p => mark t (residual p-diagonalConstant)) := by
  obtain ⟨q,hq,hpr,h₃,H⟩ := ThetaLagSignThreshold.signed hAP m
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  have hb := balanced (law_symmetric hAP hF) (empirical_tendsto hAP hF)
  obtain ⟨t,c,ht,hb,hc,h⟩ := H (fun _ => diagonalConstant) (fun _ => rfl) _ hb
  have h' := h 0
  simp only [sub_zero] at h'
  exact ⟨q,hq,hpr,h₃,t,c,ht,hc,hb,h'⟩

theorem excess (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ q : ℕ,m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ t c A : ℝ,0<t ∧ 0<c ∧ 0<A ∧
      Tendsto (primeMean (fun p => mark t (residual p-diagonalConstant))) atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop,∃ h : ℕ,0<h ∧ q∣h ∧ (h:ℝ)≤A*log X ∧
        c*X≤((pairCount X h (fun p => residual p-diagonalConstant) (sameTail t):ℝ)-
         pairCount X h (fun p => residual p-diagonalConstant) (oppositeTail t))*(log X)^2 := by
  obtain ⟨q,hq,hpr,h₃,t,c,ht,hc,hb,h'⟩ := balanced_scales hAP m
  obtain ⟨A,hA,hs⟩ := short hpr.pos hc h'
  refine ⟨q,hq,hpr,h₃,t,c,A,ht,hc,hA,hb,?_⟩
  filter_upwards [hs] with X hh
  obtain ⟨d,hd,he,hl,hs⟩ := hh
  exact ⟨d,hd,he,hl,by rwa [marked X d t] at hs⟩

#print axioms marked
#print axioms balanced
#print axioms excess
end
end Arxiv.«2501.03234».ThetaLagSignCounts
