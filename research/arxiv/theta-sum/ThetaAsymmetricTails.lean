import ThetaPrimeResidualLaw
import Mathlib.MeasureTheory.Integral.Layercake

/-! A nonzero first moment forces unequal tails at a positive two-sided
continuity level. At that level the empirical signed counts converge. -/
namespace Arxiv.«2501.03234».ThetaAsymmetricTails
open MeasureTheory Filter Real Finset ThetaPrimeLaw ThetaPrimeDensity ThetaNaturalPrimeMeans
open scoped Topology
noncomputable section

theorem atom (ν : Measure ℝ) [IsFiniteMeasure ν] (f : ℝ → ℝ) (hf : Measurable f) : ∀ᵐ t : ℝ,ν {x | f x=t}=0 := by
  apply ae_iff.mpr
  convert (Measure.countable_meas_level_set_pos (μ:=ν) hf).measure_zero volume using 2
  ext t;simp

theorem count_limit {f : ℕ → ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto (empirical f) atTop (𝓝 μ)) {s : Set ℝ} (hs : MeasurableSet s) (h₀ : (μ:Measure ℝ) (frontier s)=0) :
    Tendsto (fun X : ℕ => ((primeSet (fun p => f p∈s) X).card:ℝ)/X.primeCounting) atTop (𝓝 ((μ:Measure ℝ).real s)) := by
  have hc := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h h₀
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hc
  exact hr.congr' ((eventually_ge_atTop 2).mono (fun X hX => ThetaPrimeLaw.empirical_real_set hX f hs))

theorem level (μ : ProbabilityMeasure ℝ) {P : ℝ → Prop} (hP : ∀ᵐ t : ℝ,P t) (hm : (∫ x : ℝ,x ∂(μ:Measure ℝ))≠0) :
    ∃ t : ℝ,0<t ∧ P t ∧ (μ:Measure ℝ) {t}=0 ∧ (μ:Measure ℝ) {-t}=0 ∧
      (μ:Measure ℝ).real (Set.Ioi t)≠(μ:Measure ℝ).real (Set.Iio (-t)) := by
  let ν := (μ:Measure ℝ)
  have hint : Integrable (fun x : ℝ => x) ν := by
    by_contra hh;exact hm (integral_undef hh)
  have hp := hint.pos_part
  have hn := hint.neg_part
  have ep := hp.integral_eq_integral_meas_lt (Eventually.of_forall (fun x => le_max_right x 0))
  have en := hn.integral_eq_integral_meas_lt (Eventually.of_forall (fun x => le_max_right (-x) 0))
  by_contra! h
  have heq : (∫ x : ℝ,max x 0 ∂ν)=∫ x : ℝ,max (-x) 0 ∂ν := by
    rw [ep,en]
    apply integral_congr_ae
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards [atom ν id measurable_id,atom ν Neg.neg measurable_neg,hP] with t h₁ h₂ hp ht
    change 0<t at ht
    have ha : ν {t}=0 := h₁
    have hb : ν {-t}=0 := by
      convert h₂ using 2;ext x;simp [eq_neg_iff_add_eq_zero,neg_eq_iff_add_eq_zero,add_comm]
    have hh := h t ht hp ha hb
    have hpos : {x : ℝ | t < max x 0}=Set.Ioi t := by ext x;simp [not_lt_of_ge ht.le]
    have hneg : {x : ℝ | t < max (-x) 0}=Set.Iio (-t) := by
      ext x;simp only [Set.mem_ofPred_eq,lt_max_iff,Set.mem_Iio,not_lt_of_ge ht.le,or_false];constructor <;> intro hx <;> linarith
    simpa only [hpos,hneg] using hh
  apply hm
  change (∫ x : ℝ,x ∂ν)=0
  have eqn (x : ℝ) : x=max x 0-max (-x) 0 := by rcases le_total 0 x with h|h <;> simp [*]
  conv_lhs => arg 2;intro x;rw [eqn x]
  rw [integral_sub hp hn,heq,sub_self]

def mark (t x : ℝ) : ℝ := (if t<x then 1 else 0)-(if x< -t then 1 else 0)

theorem limit {f : ℕ → ℝ} {μ : ProbabilityMeasure ℝ} (h : Tendsto (empirical f) atTop (𝓝 μ))
    {t : ℝ} (ha : (μ:Measure ℝ) {t}=0) (hb : (μ:Measure ℝ) {-t}=0) :
    Tendsto (primeMean (fun n => mark t (f n))) atTop
      (𝓝 ((μ:Measure ℝ).real (Set.Ioi t)-(μ:Measure ℝ).real (Set.Iio (-t)))) := by
  have hh := (count_limit h measurableSet_Ioi (by simpa only [frontier_Ioi] using ha)).sub
    (count_limit h measurableSet_Iio (by simpa only [frontier_Iio] using hb))
  apply hh.congr (fun X => ?_)
  simp only [mark,primeMean,sum_sub_distrib,sum_boole,primeSet,Set.mem_Ioi,Set.mem_Iio,sub_div]

#print axioms level
#print axioms limit
end
end Arxiv.«2501.03234».ThetaAsymmetricTails
