import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! The finite adapted-contraction construction in Hua, Song and Tudose, §2.4,
following Song's Lipschitz image lemma. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace Green54Contractions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Op" => E →L[ℝ] E

private theorem defect_nonneg (A : Op) (hA : ‖A‖ ≤ 1) :
    0 ≤ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)).symm (1 - A * A.adjoint) := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · let e := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)
    have h : (1 - A * A.adjoint).adjoint = 1 - A * A.adjoint := by
      simp only [map_sub, ContinuousLinearMap.adjoint_one, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    exact (e.symm.map_star' (1 - A * star A)).symm.trans (congrArg e.symm h)
  · intro x
    let t : E := WithLp.toLp 2 x
    have hn : ‖A.adjoint t‖ ≤ ‖t‖ := calc
      _ ≤ ‖A.adjoint‖ * ‖t‖ := A.adjoint.le_opNorm _
      _ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right (by simpa using hA) (norm_nonneg _)
      _ = _ := one_mul _
    rw [star_trivial x]
    change 0 ≤ t ⬝ᵥ (_ *ᵥ t)
    rw [← Matrix.inner_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
    simp only [sub_apply, one_apply_eq_self,
      mul_apply_eq_comp, inner_sub_right, real_inner_self_eq_norm_sq,
      ← A.adjoint_inner_left, real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hn 2)

/-- The positive square root of the missing covariance, in Euclidean coordinates. -/
private def correction (A : Op) : Op :=
  let e := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)
  e (CFC.sqrt (e.symm (1 - A * A.adjoint)))

private theorem correction_continuous :
    Continuous (fun A : {A : Op // ‖A‖ ≤ 1} => correction A.val) := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)
  have he : Continuous e := e.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hei : Continuous e.symm :=
    e.symm.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hAdj : Continuous (fun A : {A : Op // ‖A‖ ≤ 1} => A.val.adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp continuous_subtype_val
  exact he.comp (CFC.continuousOn_sqrt.comp_continuous
    (hei.comp (continuous_const.sub (continuous_subtype_val.mul hAdj)))
    (fun A => defect_nonneg A.val A.property))

private theorem correction_cov (A : Op) (hA : ‖A‖ ≤ 1) :
    A * A.adjoint + correction A * (correction A).adjoint = 1 := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)
  let D := e.symm (1 - A * A.adjoint)
  have hD : 0 ≤ D := defect_nonneg A hA
  have hself : IsSelfAdjoint (correction A) := (CFC.sqrt_nonneg D).isSelfAdjoint.map e
  rw [hself.adjoint_eq]
  change A * A.adjoint + e (CFC.sqrt D) * e (CFC.sqrt D) = 1
  rw [← map_mul, CFC.sqrt_mul_sqrt_self _ hD, e.apply_symm_apply]
  abel

omit [DecidableEq ι] in
private theorem norm_split (A B : Op) (h : A * A.adjoint + B * B.adjoint = 1) (t : E) :
    ‖A.adjoint t‖ ^ 2 + ‖B.adjoint t‖ ^ 2 = ‖t‖ ^ 2 := by
  have he := congrArg (fun T : Op => ⟪t, T t⟫) h
  simpa only [add_apply, mul_apply_eq_comp,
    one_apply_eq_self, inner_add_right, ← A.adjoint_inner_left,
    ← B.adjoint_inner_left, real_inner_self_eq_norm_sq] using he

omit [DecidableEq ι] in
private theorem charFun_linear (A : Op) (t : E) :
    charFun ((stdGaussian E).map A) t = charFun (stdGaussian E) (A.adjoint t) := by
  rw [charFun_apply, charFun_apply,
    integral_map A.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [ContinuousLinearMap.adjoint_inner_right]

omit [DecidableEq ι] in
private theorem gaussian_add_linear (A B : Op)
    (h : ∀ t, ‖A.adjoint t‖ ^ 2 + ‖B.adjoint t‖ ^ 2 = ‖t‖ ^ 2) :
    MeasurePreserving (fun z : E × E => A z.1 + B z.2)
      ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  refine ⟨by fun_prop, Measure.ext_of_charFun (funext fun t => ?_)⟩
  have hmap := (Measure.map_prod_map (stdGaussian E) (stdGaussian E)
    A.continuous.measurable B.continuous.measurable)
  let : IsProbabilityMeasure ((stdGaussian E).map A) := Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure ((stdGaussian E).map B) := Measure.isProbabilityMeasure_map (by fun_prop)
  have hconv := congrFun (charFun_map_add_prod_eq_mul
    (μ := (stdGaussian E).map A) (ν := (stdGaussian E).map B)) t
  rw [hmap, Measure.map_map (by fun_prop) (by fun_prop)] at hconv
  change charFun ((stdGaussian E).prod (stdGaussian E) |>.map (fun z => A z.1 + B z.2)) t = _
  rw [show charFun (((stdGaussian E).prod (stdGaussian E)).map (fun z => A z.1 + B z.2)) t =
    charFun ((stdGaussian E).map A) t * charFun ((stdGaussian E).map B) t from hconv,
    charFun_linear, charFun_linear, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  congr 1
  have ht : (‖A.adjoint t‖ : ℂ) ^ 2 + (‖B.adjoint t‖ : ℂ) ^ 2 = (‖t‖ : ℂ) ^ 2 := by
    exact_mod_cast h t
  linear_combination - ht / 2

private abbrev Contraction (ι : Type*) [Fintype ι] :=
  {T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι // ‖T‖ ≤ 1}

private def innovation (s : Bool) (A : Contraction ι) (z : E × E) : E :=
  A.val z.1 + (if s then correction A.val else -correction A.val) z.2

private theorem innovation_continuous (s : Bool) :
    Continuous (Function.uncurry (innovation (ι := ι) s)) := by
  let D := Contraction ι × (E × E)
  have ha : Continuous (fun z : D => z.1.val) := continuous_subtype_val.comp continuous_fst
  have hb : Continuous (fun z : D => correction z.1.val) :=
    correction_continuous.comp continuous_fst
  have hu : Continuous (fun z : D => z.2.1) := continuous_fst.comp continuous_snd
  have hv : Continuous (fun z : D => z.2.2) := continuous_snd.comp continuous_snd
  cases s
  · exact (ha.clm_apply hu).add (hb.neg.clm_apply hv)
  · exact (ha.clm_apply hu).add (hb.clm_apply hv)

private theorem innovation_preserving (s : Bool) (A : Contraction ι) :
    MeasurePreserving (innovation s A) ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  have h := norm_split _ _ (correction_cov A.val A.property)
  cases s
  · apply gaussian_add_linear A.val (-correction A.val)
    simpa only [map_neg, neg_apply, norm_neg] using h
  · exact gaussian_add_linear _ _ h

private theorem innovations_sum (A : Contraction ι) (z : E × E) :
    innovation true A z + innovation false A z = (2 : ℝ) • A.val z.1 := by
  simp only [innovation, if_true, Bool.false_eq_true, if_false, neg_apply, two_smul]
  abel

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
private def past {n : ℕ} (i : Fin n) (x : Fin n → V) : Fin i.val → V :=
  fun j => x ⟨j.val, j.isLt.trans i.isLt⟩

private def splitLast (V : Type*) [MeasurableSpace V] (n : ℕ) :
    (Fin (n + 1) → V) ≃ᵐ (Fin n → V) × V :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => V) (Fin.last n)).trans
    MeasurableEquiv.prodComm

private theorem splitLast_apply {n : ℕ} (x : Fin (n + 1) → V) :
    splitLast V n x = (fun i => x i.castSucc, x (Fin.last n)) := by
  change (fun j => x ((Fin.last n).succAbove j), x (Fin.last n)) = _
  simp only [Fin.succAbove_last_apply]

private theorem splitLast_preserving (μ : Measure V) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (splitLast V n) (Measure.pi fun _ => μ) ((Measure.pi fun _ => μ).prod μ) :=
  Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => μ) (Fin.last n))

/-- A triangular transform with measure-preserving innovation at each history preserves
the product law. The transform may depend on the entire preceding input. -/
private theorem triangular_preserving (μ : Measure V) (ν : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (f : (i : Fin n) → (Fin i.val → V) → V → W)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hμ : ∀ i u, (μ.map (f i u)) = ν) :
    MeasurePreserving (fun (x : Fin n → V) i => f i (past i x) (x i))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => ν) := by
  induction n with
  | zero =>
    have hm : Measurable (fun (x : Fin 0 → V) (i : Fin 0) => f i (past i x) (x i)) :=
      measurable_pi_iff.mpr (fun i => i.elim0)
    refine ⟨hm, ?_⟩
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) Fin.elim0,
      Measure.pi_of_empty (fun _ : Fin 0 => ν) Fin.elim0, Measure.map_dirac' hm]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hprev := ih (fun i => f i.castSucc) (fun i => hf i.castSucc) (fun i => hμ i.castSucc)
    have hstep := hprev.skew_product (hf (Fin.last n))
      (ae_of_all _ (fun x => hμ (Fin.last n) x))
    have whole := (splitLast_preserving ν n).symm.comp (hstep.comp (splitLast_preserving μ n))
    have hfun : (fun (x : Fin (n + 1) → V) i => f i (past i x) (x i)) =
        (splitLast W n).symm ∘ (fun p => ((fun i : Fin n => f i.castSucc (past i p.1) (p.1 i)),
          f (Fin.last n) p.1 p.2)) ∘ (splitLast V n) := by
      funext x
      apply (splitLast W n).injective
      rw [Function.comp_apply, MeasurableEquiv.apply_symm_apply, Function.comp_apply,
        splitLast_apply, splitLast_apply]
      rfl
    rw [hfun]
    exact whole

private def normalizedSum (n : ℕ) (x : Fin n → E) : E :=
  (Real.sqrt n)⁻¹ • ∑ i, x i

omit [DecidableEq ι] in
private theorem normalizedSum_preserving {n : ℕ} (hn : 0 < n) :
    MeasurePreserving (normalizedSum (ι := ι) n)
      (Measure.pi fun _ => stdGaussian E) (stdGaussian E) := by
  refine ⟨by unfold normalizedSum; fun_prop, Measure.ext_of_charFun (funext fun t => ?_)⟩
  let c : ℝ := (Real.sqrt n)⁻¹
  have hmap : (Measure.pi (fun _ : Fin n => stdGaussian E)).map (normalizedSum n) =
      ((Measure.pi (fun _ : Fin n => stdGaussian E)).map (fun x => ∑ i, x i)).map
        (fun x => c • x) := (Measure.map_map (by fun_prop) (by fun_prop)).symm
  rw [hmap, charFun_map_smul,
    congrFun (charFun_map_sum_pi_eq_prod (fun _ : Fin n => stdGaussian E)) (c • t)]
  simp only [Finset.prod_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    charFun_stdGaussian, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ c by positivity),
    Complex.ofReal_mul]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hc : ((n : ℕ) : ℂ) * (c : ℂ)^2 = 1 := by
    have hs : (n : ℝ) * c^2 = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt (by positivity), mul_inv_cancel₀ (by positivity)]
    exact_mod_cast hs
  linear_combination -(‖t‖ : ℂ)^2 / 2 * hc

/-- The normalized sum of Gaussian increments after applying a linear map at each
time. Its coefficient is evaluated only on the preceding increments. -/
def contractedSum {n : ℕ} (A : (i : Fin n) → (Fin i.val → E) → Op) (x : Fin n → E) : E :=
  (Real.sqrt n)⁻¹ • ∑ i, A i (past i x) (x i)

omit [DecidableEq ι] in
private theorem pair_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u v : Ω → E) (hu : MeasurePreserving u μ (stdGaussian E))
    (hv : MeasurePreserving v μ (stdGaussian E)) :
    ∃ ρ : ProbabilityMeasure (E × E),
      (ρ : Measure (E × E)).map Prod.fst = stdGaussian E ∧
      (ρ : Measure (E × E)).map Prod.snd = stdGaussian E ∧
      (ρ : Measure (E × E)).map (fun z => (2 : ℝ)⁻¹ • (z.1 + z.2)) =
        μ.map (fun w => (2 : ℝ)⁻¹ • (u w + v w)) := by
  let p (w : Ω) := (u w, v w)
  have hp : Measurable p := hu.measurable.prodMk hv.measurable
  refine ⟨⟨μ.map p, Measure.isProbabilityMeasure_map hp.aemeasurable⟩, ?_, ?_, ?_⟩
  · exact (Measure.map_map measurable_fst hp).trans hu.map_eq
  · exact (Measure.map_map measurable_snd hp).trans hv.map_eq
  · exact Measure.map_map (by fun_prop) hp

/-- Every normalized predictable sum of contractions of independent standard Gaussian
increments is the midpoint of two vectors with standard Gaussian marginal laws. -/
theorem adapted_gaussian_midpoint {n : ℕ} (hn : 0 < n)
    (A : (i : Fin n) → (Fin i.val → E) → Op) (hm : ∀ i, Measurable (A i))
    (hA : ∀ i u, ‖A i u‖ ≤ 1) :
    ∃ ρ : ProbabilityMeasure (E × E),
      (ρ : Measure (E × E)).map Prod.fst = stdGaussian E ∧
      (ρ : Measure (E × E)).map Prod.snd = stdGaussian E ∧
      (ρ : Measure (E × E)).map (fun z => (2 : ℝ)⁻¹ • (z.1 + z.2)) =
        (Measure.pi (fun _ : Fin n => stdGaussian E)).map (contractedSum A) := by
  let γ := stdGaussian E
  let P := Measure.pi (fun _ : Fin n => γ.prod γ)
  let fstPath (x : Fin n → E × E) (i : Fin n) := (x i).1
  have hfirst : MeasurePreserving fstPath P (Measure.pi fun _ : Fin n => γ) :=
    triangular_preserving (γ.prod γ) γ n (fun _ _ z => z.1)
      (fun _ => measurable_fst.comp measurable_snd) (fun _ _ => measurePreserving_fst.map_eq)
  let T (i : Fin n) (u : Fin i.val → E × E) : Contraction ι :=
    ⟨A i (fun j => (u j).1), hA _ _⟩
  have hT (i : Fin n) : Measurable (T i) :=
    ((hm i).comp (measurable_pi_iff.mpr fun j => measurable_fst.comp (measurable_pi_apply j))).subtype_mk
  let path (s : Bool) (x : Fin n → E × E) (i : Fin n) :=
    innovation s (T i (past i x)) (x i)
  have hpath (s : Bool) : MeasurePreserving (path s) P (Measure.pi fun _ : Fin n => γ) :=
    triangular_preserving (γ.prod γ) γ n (fun i u z => innovation s (T i u) z)
      (fun i => (innovation_continuous (ι := ι) s).measurable.comp
        (((hT i).comp measurable_fst).prodMk measurable_snd))
      (fun i u => (innovation_preserving s (T i u)).map_eq)
  let out (s : Bool) := normalizedSum n ∘ path s
  have hout (s : Bool) : MeasurePreserving (out s) P γ :=
    (normalizedSum_preserving hn).comp (hpath s)
  obtain ⟨ρ, h₁, h₂, hhalf⟩ := pair_law P _ _ (hout true) (hout false)
  refine ⟨ρ, h₁, h₂, hhalf.trans ?_⟩
  have hmC : Measurable (contractedSum A) := by
    unfold contractedSum
    have heval : Continuous (fun z : Op × E => z.1 z.2) := continuous_fst.clm_apply continuous_snd
    have hterm (i : Fin n) : Measurable (fun x : Fin n → E => A i (past i x) (x i)) := by
      have hp : Measurable (past (V := E) i) :=
        measurable_pi_iff.mpr fun j => measurable_pi_apply (⟨j.val, j.isLt.trans i.isLt⟩ : Fin n)
      exact heval.measurable.comp (((hm i).comp hp).prodMk (measurable_pi_apply i))
    exact (show Measurable (fun _ : Fin n → E => (Real.sqrt n)⁻¹) from measurable_const).smul
      (Finset.measurable_fun_sum Finset.univ fun i _ => hterm i)
  rw [← hfirst.map_eq, Measure.map_map hmC hfirst.measurable]
  congr 1
  funext x
  change (2 : ℝ)⁻¹ • ((Real.sqrt n)⁻¹ • ∑ i, path true x i +
    (Real.sqrt n)⁻¹ • ∑ i, path false x i) = _
  rw [← smul_add, ← Finset.sum_add_distrib]
  simp only [path, innovations_sum, ← Finset.smul_sum]
  rw [smul_comm (Real.sqrt n)⁻¹, ← mul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  rfl

section Compact
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

/-- Laws of midpoints of pairs with the given marginal law on both coordinates. -/
def midpointLaws (γ : Measure F) : Set (ProbabilityMeasure F) :=
  {μ | ∃ ρ : ProbabilityMeasure (F × F), (ρ : Measure (F × F)).map Prod.fst = γ ∧
    (ρ : Measure (F × F)).map Prod.snd = γ ∧
    (ρ : Measure (F × F)).map (fun z => (2 : ℝ)⁻¹ • (z.1 + z.2)) = (μ : Measure F)}

/-- Midpoint laws with fixed marginals are weakly compact. -/
theorem isCompact_midpointLaws (γ : Measure F) [IsProbabilityMeasure γ] :
    IsCompact (midpointLaws γ) := by
  let Γ : ProbabilityMeasure F := ⟨γ, inferInstance⟩
  let S : Set (ProbabilityMeasure (F × F)) :=
    {ρ | ρ.map continuous_fst.measurable.aemeasurable = Γ ∧
        ρ.map continuous_snd.measurable.aemeasurable = Γ}
  have hc : IsClosed S :=
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
      (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)
  have hK : IsCompact S := by
    rw [← hc.closure_eq]
    apply isCompact_closure_of_isTightMeasureSet
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := γ)).subset
      rintro _ ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
      exact congrArg (fun μ : ProbabilityMeasure F => (μ : Measure F)) hρ.1
    · apply (isTightMeasureSet_singleton (μ := γ)).subset
      rintro _ ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
      exact congrArg (fun μ : ProbabilityMeasure F => (μ : Measure F)) hρ.2
  let m (z : F × F) := (2 : ℝ)⁻¹ • (z.1 + z.2)
  have hm : Continuous m := by unfold m; fun_prop
  convert hK.image (ProbabilityMeasure.continuous_map hm) using 1
  ext μ
  constructor
  · rintro ⟨ρ, hf, hs, he⟩
    exact ⟨ρ, ⟨ProbabilityMeasure.toMeasure_injective hf, ProbabilityMeasure.toMeasure_injective hs⟩,
      ProbabilityMeasure.toMeasure_injective he⟩
  · rintro ⟨ρ, ⟨hf, hs⟩, rfl⟩
    exact ⟨ρ, congrArg (fun ν : ProbabilityMeasure F => (ν : Measure F)) hf,
      congrArg (fun ν : ProbabilityMeasure F => (ν : Measure F)) hs, rfl⟩
end Compact

/-- All finite predictable contraction laws, allowing the number of time steps to vary. -/
def adaptedLaws (ι : Type*) [Fintype ι] : Set (ProbabilityMeasure (EuclideanSpace ℝ ι)) :=
  {ν | ∃ (n : ℕ) (_ : 0 < n) (A : (i : Fin n) → (Fin i.val → EuclideanSpace ℝ ι) →
        (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)),
      (∀ i, Measurable (A i)) ∧ (∀ i u, ‖A i u‖ ≤ 1) ∧
      (Measure.pi (fun _ : Fin n => stdGaussian (EuclideanSpace ℝ ι))).map (contractedSum A) =
        (ν : Measure (EuclideanSpace ℝ ι))}

/-- Every weak limit of finite adapted contraction laws admits a Gaussian midpoint coupling. -/
theorem closure_adaptedLaws_subset :
    closure (adaptedLaws ι) ⊆ midpointLaws (stdGaussian E) := by
  apply closure_minimal _ (isCompact_midpointLaws (stdGaussian E)).isClosed
  rintro ν ⟨n, hn, A, hm, hA, he⟩
  obtain ⟨ρ, h₁, h₂, hout⟩ := adapted_gaussian_midpoint hn A hm hA
  exact ⟨ρ, h₁, h₂, hout.trans he⟩

#print axioms adapted_gaussian_midpoint
#print axioms isCompact_midpointLaws
#print axioms closure_adaptedLaws_subset

end Green54Contractions
