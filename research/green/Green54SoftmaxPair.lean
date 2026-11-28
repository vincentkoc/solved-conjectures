import Green54LangevinLimits
import Green54Softmax
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Analysis.InnerProductSpace.Dual
/-! The two-Gaussian representation for the softmax conditional laws in Green 54.
Jensen's inequality supplies a supporting hyperplane for log-sum-exp. Each softmax weight
has a global Lipschitz bound because it lies in (0,1]. -/

open Green54Softmax MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace Green54SoftmaxPair
variable {I E : Type*} [Fintype I] [Nonempty I] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private def normalizer (w : Scores I E) (x : E) := ∑ i, Real.exp (affineScore w i x)
omit [CompleteSpace E] in
private theorem zpos (w : Scores I E) (x : E) : 0 < normalizer w x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
omit [CompleteSpace E] in
private theorem wpos (w : Scores I E) (i : I) (x : E) : 0 < weight w i x :=
  div_pos (Real.exp_pos _) (zpos w x)
omit [CompleteSpace E] in
private theorem wsum (w : Scores I E) (x : E) : ∑ i, weight w i x = 1 := by
  simp only [weight, ←Finset.sum_div]
  exact div_self (zpos w x).ne'

private def slope (w : Scores I E) (i : I) : E := (InnerProductSpace.toDual ℝ E).symm (w.2 i)
private def avgSlope (w : Scores I E) (x : E) : E := ∑ i, weight w i x • slope w i
private theorem log_support (w : Scores I E) (x y : E) :
    ⟪avgSlope w x,y-x⟫ ≤ logPartition w y-logPartition w x := by
  have h := (convexOn_exp : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp).map_sum_le (t := Finset.univ) (w := fun i => weight w i x) (p := fun i => w.2 i (y-x))
    (fun i _ => (wpos w i x).le) (wsum w x) (fun i _ => Set.mem_univ (w.2 i (y-x)))
  have hterm (i : I) : weight w i x * Real.exp (w.2 i (y-x)) =
      Real.exp (affineScore w i y)/normalizer w x := by
    change (Real.exp (affineScore w i x)/normalizer w x)*_ = _
    rw [div_mul_eq_mul_div,← Real.exp_add]
    simp only [affineScore,map_sub]
    ring_nf
  have he : Real.exp (∑ i, weight w i x*(w.2 i (y-x))) ≤ normalizer w y /normalizer w x := by
    simpa only [smul_eq_mul,hterm,← Finset.sum_div,normalizer] using h
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp,Real.log_div (zpos w y).ne' (zpos w x).ne'] at hl
  simpa only [logPartition,logSum,normalizer,affineScore,avgSlope,sum_inner,real_inner_smul_left,slope,InnerProductSpace.toDual_symm_apply] using hl

/-- Negative log-density of one softmax component, up to a constant. -/
def potential (w : Scores I E) (i : I) (x : E) := ‖x‖^2/2 + logPartition w x-affineScore w i x
/-- Identity plus the weighted mean slope minus the selected slope. -/
def drift (w : Scores I E) (i : I) (x : E) := x+avgSlope w x-slope w i
/-- The drift supports the component potential at every point. -/
theorem drift_subgradient (w : Scores I E) (i : I) (x y : E) :
    ⟪drift w i x,y-x⟫ ≤ potential w i y-potential w i x := by
  have h := log_support w x y
  have he := norm_sub_sq_real y x
  rw [real_inner_comm x y] at he
  simp only [drift,inner_sub_left,inner_add_left,slope,InnerProductSpace.toDual_symm_apply,
    potential,affineScore,map_sub]
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖y-x‖]
/-- The Gaussian quadratic term gives modulus one of strong monotonicity. -/
theorem drift_monotone (w : Scores I E) (i : I) (x y : E) :
    ‖x-y‖^2 ≤ ⟪x-y,drift w i x-drift w i y⟫ := by
  have h := log_support w x y
  have h' := log_support w y x
  rw [←neg_sub x y,inner_neg_right] at h
  rw [show drift w i x-drift w i y = (x-y)+(avgSlope w x-avgSlope w y) by unfold drift; abel,
    inner_add_right,real_inner_self_eq_norm_sq,inner_sub_right,
    real_inner_comm (avgSlope w x) (x-y),real_inner_comm (avgSlope w y) (x-y)]
  linarith
private def slopeBound (w : Scores I E) : NNReal := ∑ j, ‖w.2 j‖₊
omit [Nonempty I] in
private theorem slope_le (w : Scores I E) (i : I) : ‖slope w i‖ ≤ (slopeBound w : ℝ) := by
  simp only [slope,LinearIsometryEquiv.norm_map,slopeBound,NNReal.coe_sum,coe_nnnorm]
  exact Finset.single_le_sum (f := fun j => ‖w.2 j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
private theorem avg_norm (w : Scores I E) (x : E) : ‖avgSlope w x‖ ≤ (slopeBound w : ℝ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, weight w i x*(slopeBound w : ℝ) := Finset.sum_le_sum fun i _ => by
      rw [norm_smul,Real.norm_of_nonneg (wpos w i x).le]
      exact mul_le_mul_of_nonneg_left (slope_le w i) (wpos w i x).le
    _ = _ := by rw [←Finset.sum_mul,wsum,one_mul]
private theorem partition_upper (w : Scores I E) (x y : E) :
    logPartition w x-logPartition w y ≤ slopeBound w * ‖x-y‖ := by
  have he := log_support w x y
  rw [←neg_sub x y,inner_neg_right] at he
  exact (by linarith : logPartition w x-logPartition w y ≤ ⟪avgSlope w x,x-y⟫).trans
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (avg_norm w x) (norm_nonneg _)))
private theorem partition_lip (w : Scores I E) : LipschitzWith (slopeBound w) (logPartition w) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,dist_eq_norm]
  apply abs_le.mpr
  exact ⟨by have h := partition_upper w y x; rw [norm_sub_rev y x] at h; linarith, partition_upper w x y⟩

omit [CompleteSpace E] in
private theorem weight_le_one (w : Scores I E) (i : I) (x : E) : weight w i x ≤ 1 := by
  rw [← wsum w x]
  exact Finset.single_le_sum (f := fun j => weight w j x) (fun j _ => (wpos w j x).le) (Finset.mem_univ i)
private theorem log_uncontracts {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    |u-v| ≤ |Real.log u-Real.log v| := by
  have h {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h₁ : b ≤ 1) (hab : a ≤ b) :
      b-a ≤ Real.log b-Real.log a := by
    have hs := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at hs
    have he := (le_div_iff₀ hb).mp (by linarith : Real.log a-Real.log b+1 ≤ a/b)
    nlinarith [mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr (Real.log_le_log ha hab))]
  rcases le_total u v with he|he
  · rw [abs_of_nonpos (sub_nonpos.mpr he),abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hu he))]
    linarith [h hu hv hv1 he]
  · rw [abs_of_nonneg (sub_nonneg.mpr he),abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hv he))]
    exact h hv hu hu1 he

private theorem weight_lip (w : Scores I E) (i : I) :
    LipschitzWith (‖w.2 i‖₊+slopeBound w) (weight w i) := by
  have h (x : E) : Real.log (weight w i x) = affineScore w i x-logPartition w x := by
    change Real.log (Real.exp (affineScore w i x)/normalizer w x) = _
    rw [Real.log_div (Real.exp_pos _).ne' (zpos w x).ne',Real.log_exp]
    rfl
  have hl : LipschitzWith ‖w.2 i‖₊ (affineScore w i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [affineScore,dist_add_left] using (w.2 i).lipschitz.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  apply (log_uncontracts (wpos w i x) (wpos w i y) (weight_le_one w i x) (weight_le_one w i y)).trans
  rw [h,h]
  exact (hl.sub (partition_lip w)).dist_le_mul x y

/-- Every finite set of slopes gives a finite global Lipschitz constant for the drift. -/
theorem drift_lipschitz (w : Scores I E) (i : I) : ∃ L : NNReal, LipschitzWith L (drift w i) := by
  let k (j : I) := (‖w.2 j‖₊+slopeBound w)*‖slope w j‖₊
  have hl (j : I) : LipschitzWith (k j) (fun x => weight w j x • slope w j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,←sub_smul,norm_smul,dist_eq_norm]
    have h := (weight_lip w j).norm_sub_le x y
    change _ ≤ (((‖w.2 j‖₊+slopeBound w)*‖slope w j‖₊ : NNReal):ℝ)*‖x-y‖
    push_cast at h ⊢
    nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (slope w j))]
  have ha : LipschitzWith (∑ j, k j) (avgSlope w) := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    rw [dist_eq_norm]; unfold avgSlope; rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    simpa only [NNReal.coe_sum,Finset.sum_mul,dist_eq_norm] using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hl j).norm_sub_le x y)
  refine ⟨1+∑ j,k j,LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simpa only [drift,dist_sub_right,id_eq] using (LipschitzWith.id.add ha).dist_le_mul x y

section Moments
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι
private theorem standard_density :
    stdGaussian V = (volume : Measure V).withDensity (fun x => ENNReal.ofReal (Green54GaussianKernel.gaussianDensity 0 1 x)) := by
  have h := Green54GaussianKernel.affine_gaussian_density (0:V) 1 one_ne_zero
  simp only [one_smul,zero_add,one_pow] at h
  change (stdGaussian V).map id = (volume : Measure V).withDensity (fun x => ENNReal.ofReal (Green54GaussianKernel.gaussianDensity 0 1 x)) at h
  simpa only [Measure.map_id] using h
private theorem moments_of_domination {π : Measure V} [IsProbabilityMeasure π] {c : ℝ≥0∞}
    (hπ : π ≤ c • stdGaussian V) (hc : c ≠ ∞) {G : V → V} {L : NNReal} (hG : LipschitzWith L G) :
    Integrable (id : V → V) π ∧
      Integrable (fun s : V × V => (‖G s.1‖+2*‖s.2‖)^3) (π.prod (stdGaussian V)) := by
  have hg := IsGaussian.memLp_id (stdGaussian V) 3 (by norm_num)
  have hπ₃ := (hg.smul_measure hc).mono_measure hπ
  refine ⟨hπ₃.integrable (by norm_num),?_⟩
  have hl : LipschitzWith L (fun x => G x-G 0) :=
    LipschitzWith.of_dist_le_mul fun x y => by simpa only [dist_sub_right] using hG.dist_le_mul x y
  have hn : MemLp G 3 π := by
    have h := (hl.comp_memLp (sub_self _) hπ₃).add (memLp_const (G 0))
    exact (memLp_congr_ae (g := G) (ae_of_all _ fun x => sub_add_cancel (G x) (G 0))).mp h
  have ha := hn.norm.comp_fst (stdGaussian V)
  have hb := hg.norm.comp_snd π
  have hj : MemLp (fun s : V × V => ‖G s.1‖+2*‖s.2‖) 3 (π.prod (stdGaussian V)) :=
    ha.add (hb.const_mul (2:ℝ))
  have h := hj.integrable_norm_rpow (by norm_num) (by norm_num)
  have hn (s : V × V) : ‖‖G s.1‖+2*‖s.2‖‖ = ‖G s.1‖+2*‖s.2‖ := Real.norm_of_nonneg (by positivity)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,hn] using h

end Moments

section Gaussian
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι
open Green54GaussianKernel Green54LangevinLimits
private def gaussConst (ι : Type*) [Fintype ι] := (Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι

private theorem density_eq (w : Scores I V) (p : I → ℝ) (i : I) (x : V) :
    gaussianDensity (0:V) 1 x * density p w i x =
      (gaussConst ι / p i)*Real.exp (-potential w i x) := by
  have hexp : Real.exp (logPartition w x) = normalizer w x := Real.exp_log (zpos w x)
  have haux : -potential w i x = -‖x‖^2/2 + affineScore w i x - logPartition w x := by unfold potential; ring
  rw [haux, Real.exp_sub,Real.exp_add,hexp]
  simp only [gaussianDensity,NNReal.coe_one,mul_one,sub_zero,density,weight,gaussConst,normalizer]
  ring

private theorem conditional_sum (w : Scores I V) (p : I → ℝ) (i : I) (hp : 0 < p i)
    (hm : ∫ x, density p w i x ∂stdGaussian V = 1) :
    let τ := (stdGaussian V).withDensity (fun x => ENNReal.ofReal (density p w i x))
    Integrable (id : V → V) τ ∧ ∃ ρ : ProbabilityMeasure (V × V),
      (ρ : Measure (V × V)).map Prod.fst = stdGaussian V ∧
      (ρ : Measure (V × V)).map Prod.snd = stdGaussian V ∧
      (ρ : Measure (V × V)).map (fun z => z.1+z.2) = τ.map (fun x => x-(∫ y,y ∂τ)) := by
  let γ := stdGaussian V
  let f := density p w i
  let τ := γ.withDensity (fun x => ENNReal.ofReal (f x))
  have hf0 (x : V) : 0 ≤ f x := (div_pos (wpos w i x) hp).le
  have hf1 (x : V) : f x ≤ 1/p i := div_le_div_of_nonneg_right (weight_le_one w i x) hp.le
  have hfm : Measurable f := (weight_lip w i).continuous.measurable.div_const _
  have hi : Integrable f γ := Integrable.of_bound hfm.aestronglyMeasurable (1/p i)
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hf0 x)]; exact hf1 x)
  let : IsProbabilityMeasure τ := ⟨by
    rw [show τ = γ.withDensity (fun x => ENNReal.ofReal (f x)) from rfl,withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf0)]
    rw [show (∫ x, f x ∂γ) = 1 from hm,ENNReal.ofReal_one]⟩
  have hdom : τ ≤ ENNReal.ofReal (1/p i) • γ := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (hf1 x))
  obtain ⟨L,hL⟩ := drift_lipschitz w i
  obtain ⟨hid,hM⟩ := moments_of_domination hdom ENNReal.ofReal_ne_top hL
  let g (x : V) := ENNReal.ofReal (gaussianDensity (0:V) 1 x)
  have hg : Measurable g := by unfold g gaussianDensity; fun_prop
  have hτ : τ = volume.withDensity (fun x => ENNReal.ofReal ((gaussConst ι /p i)*Real.exp (-potential w i x))) := by
    change ((stdGaussian V).withDensity (fun x => ENNReal.ofReal (f x))) = _
    rw [standard_density,←withDensity_mul _ hg hfm.ennreal_ofReal]
    congr 1
    funext x
    change ENNReal.ofReal (gaussianDensity (0:V) 1 x)*ENNReal.ofReal (density p w i x) = _
    rw [← ENNReal.ofReal_mul (by unfold gaussianDensity; positivity),density_eq]
  have hUm : Measurable (potential w i) := by
    unfold potential
    exact ((measurable_norm.pow_const 2 |>.div_const (2:ℝ)).add (partition_lip w).continuous.measurable).sub
      (measurable_const.add (w.2 i).continuous.measurable)
  have hc : 0 < gaussConst ι /p i := by unfold gaussConst; positivity
  have h := strongly_convex_sum hUm hL (drift_subgradient w i) (drift_monotone w i) hc
    (⟨τ,inferInstance⟩ : ProbabilityMeasure V) hτ hid hM
  exact ⟨hid,h⟩
end Gaussian

section Coordinates
open Green54Projections Green54ConvexTests
variable {J : Finset ℕ}
local notation "V" => EuclideanSpace ℝ J
local notation "A" => (J → ℝ)
/-- The translated two-Gaussian representation in the original coordinate space of a
finite softmax component, with its prescribed linear moments. -/
theorem coordinate_pair (w : Scores I A) (p : I → ℝ) (i : I) (hp : 0 < p i) (m : A)
    (hf : Continuous (density p w i)) (hm : ∫ x, density p w i x ∂finiteGaussian J = 1)
    (hbar : ∀ v : A →L[ℝ] ℝ, (∫ x, density p w i x*v x ∂finiteGaussian J) = v m) :
    ∃ ρ : ProbabilityMeasure (A × A), (ρ : Measure (A × A)).map Prod.fst = finiteGaussian J ∧
      (ρ : Measure (A × A)).map Prod.snd = finiteGaussian J ∧
      (ρ : Measure (A × A)).map (fun z => m+z.1+z.2) =
        (finiteGaussian J).withDensity (fun x => ENNReal.ofReal (density p w i x)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℝ)
  let we : Scores I V := (w.1,fun j => (w.2 j).comp e.toContinuousLinearMap)
  let d := density p w i
  let τ := (stdGaussian V).withDensity (fun x => ENNReal.ofReal (density p we i x))
  let ν := (finiteGaussian J).withDensity (fun x => ENNReal.ofReal (d x))
  have hdown := (PiLp.continuous_ofLp 2 (fun _ : J => ℝ)).measurable
  have hd : MeasurePreserving (WithLp.ofLp : V → A) (stdGaussian V) (finiteGaussian J) := by
    refine ⟨hdown,?_⟩
    rw [← map_pi_eq_stdGaussian, Measure.map_map hdown (PiLp.continuous_toLp 2 _).measurable]
    exact Measure.map_id
  have hmass : (∫ x, density p we i x ∂stdGaussian V) = 1 := by
    have h := integral_map (μ := stdGaussian V) hd.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hd.map_eq] at h
    exact h.symm.trans hm
  have hτ : τ.map (WithLp.ofLp : V → A) = ν := by
    ext s hs
    rw [Measure.map_apply hdown hs]
    change ((stdGaussian V).withDensity (fun x => ENNReal.ofReal (d x.ofLp))) _ = _
    rw [withDensity_apply _ (hdown hs)]
    change _ = ((finiteGaussian J).withDensity (fun x => ENNReal.ofReal (d x))) s
    rw [withDensity_apply _ hs,← hd.map_eq, setLIntegral_map hs hf.measurable.ennreal_ofReal hdown]
  obtain ⟨hi,ρ,h₁,h₂,hs⟩ := conditional_sum we p i hp hmass
  have hmean (j : J) : (∫ y, y ∂τ) j = m j := by
    let v : A →L[ℝ] ℝ := ContinuousLinearMap.proj j
    let L := v.comp e.toContinuousLinearMap
    have hd0 (x : A) : 0 ≤ d x := (div_pos (div_pos (Real.exp_pos _) (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)) hp).le
    have hpi := integral_map (μ := τ) hdown.aemeasurable v.continuous.aestronglyMeasurable
    rw [hτ] at hpi
    change L (∫ y, y ∂τ) = _
    calc
      _ = ∫ x, L x ∂τ := (L.integral_comp_comm (φ := fun x => x) hi).symm
      _ = ∫ x, v x ∂ν := hpi.symm
      _ = ∫ x, d x*v x ∂finiteGaussian J := by
        unfold ν
        rw [integral_withDensity_eq_integral_toReal_smul hf.measurable.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae (ae_of_all _ fun x => ?_)
        change (ENNReal.ofReal (d x)).toReal * v x = d x * v x
        rw [ENNReal.toReal_ofReal (hd0 x)]
      _ = m j := hbar v
  let pmap (z : V × V) := (z.1.ofLp,z.2.ofLp)
  have hpm : Measurable pmap := (hdown.comp measurable_fst).prodMk (hdown.comp measurable_snd)
  let ρ' := ρ.map hpm.aemeasurable
  refine ⟨ρ',?_,?_,?_⟩
  · change ((ρ : Measure (V × V)).map pmap).map Prod.fst = _
    rw [Measure.map_map measurable_fst hpm]
    exact ((Measure.map_map hdown measurable_fst).symm.trans (congrArg (Measure.map WithLp.ofLp) h₁)).trans hd.map_eq
  · change ((ρ : Measure (V × V)).map pmap).map Prod.snd = _
    rw [Measure.map_map measurable_snd hpm]
    exact ((Measure.map_map hdown measurable_snd).symm.trans (congrArg (Measure.map WithLp.ofLp) h₂)).trans hd.map_eq
  · let re (x : V) := m+x.ofLp
    have hr : Measurable re := measurable_const.add hdown
    have he : (fun z : A × A => m+z.1+z.2) ∘ pmap = re ∘ (fun z : V × V => z.1+z.2) := by
      funext z j;change m j+z.1 j+z.2 j=m j+(z.1 j+z.2 j); ring
    change ((ρ : Measure (V × V)).map pmap).map _ = ν
    rw [Measure.map_map (by fun_prop) hpm,he,←Measure.map_map hr (by fun_prop),hs,Measure.map_map hr (by fun_prop),← hτ]
    congr 1
    funext x j
    change m j + (x j-(∫ y,y ∂τ) j) = x j
    rw [hmean]
    ring
end Coordinates

#print axioms drift_subgradient
#print axioms drift_monotone
#print axioms drift_lipschitz
#print axioms coordinate_pair
end Green54SoftmaxPair
