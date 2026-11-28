import Green54Softmax

/-! Mixing conditional two-Gaussian couplings to obtain the Green 54 triple. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise
open Green54ConvexTests Green54Projections Green54FiniteLaws Green54Softmax

namespace Green54GaussianTilts
variable {E I : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [Fintype I]

/-- Mix the translated pair couplings using the target atom masses. In each component
the three coordinates sum to its atom, while the first marginal mixes to the reference law. -/
theorem mix_pairs (γ : Measure E) [IsProbabilityMeasure γ]
    (hreflect : γ.map (fun x => -x) = γ) (p : I → ℝ≥0∞) (hp : ∑ i, p i = 1)
    (m : I → E) (τ : I → Measure E) (hmix : ∑ i, p i • τ i = γ)
    (ρ : I → ProbabilityMeasure (E × E))
    (hfst : ∀ i, (ρ i : Measure (E × E)).map Prod.fst = γ)
    (hsnd : ∀ i, (ρ i : Measure (E × E)).map Prod.snd = γ)
    (ht : ∀ i, (ρ i : Measure (E × E)).map (fun z => m i + z.1 + z.2) = τ i) :
    ∃ π : ProbabilityMeasure (Fin 3 → E),
      (∀ k, (π : Measure (Fin 3 → E)).map (fun z => z k) = γ) ∧
      (π : Measure (Fin 3 → E)).map (fun z => z 0 + z 1 + z 2) = ∑ i, p i • Measure.dirac (m i) := by
  let T (i : I) (z : E × E) : Fin 3 → E := ![m i + z.1 + z.2, -z.1, -z.2]
  have hT (i) : Measurable (T i) := by
    apply measurable_pi_lambda
    intro k
    fin_cases k <;> simp [T] <;> fun_prop
  let πi (i : I) := (ρ i).map (hT i).aemeasurable
  let μ : Measure (Fin 3 → E) := ∑ i, p i • (πi i : Measure (Fin 3 → E))
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simpa [μ, Measure.finsetSum_apply] using hp
  let π : ProbabilityMeasure (Fin 3 → E) := ⟨μ, hprob⟩
  have push (f : (Fin 3 → E) → E) (hf : Measurable f) :
      (π : Measure (Fin 3 → E)).map f = ∑ i, p i • (ρ i : Measure (E × E)).map (f ∘ T i) := by
    change (∑ i, p i • (πi i : Measure (Fin 3 → E))).map f = _
    rw [Measure.map_finset_sum hf.aemeasurable]
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.map_smul, show (πi i : Measure (Fin 3 → E)) = (ρ i : Measure (E × E)).map (T i) from rfl,
      Measure.map_map hf (hT i)]
  refine ⟨π, fun k => ?_, ?_⟩
  · rw [push _ (measurable_pi_apply k)]
    fin_cases k
    · change ∑ i, p i • (ρ i : Measure (E × E)).map (fun z => m i + z.1 + z.2) = γ
      simpa only [ht] using hmix
    · have h (i) : (ρ i : Measure (E × E)).map ((fun x : E => -x) ∘ Prod.fst) = γ := by
        rw [← Measure.map_map measurable_neg measurable_fst, hfst, hreflect]
      change ∑ i, p i • (ρ i : Measure (E × E)).map ((fun x : E => -x) ∘ Prod.fst) = γ
      simp only [h, ← Finset.sum_smul, hp, one_smul]
    · have h (i) : (ρ i : Measure (E × E)).map ((fun x : E => -x) ∘ Prod.snd) = γ := by
        rw [← Measure.map_map measurable_neg measurable_snd, hsnd, hreflect]
      change ∑ i, p i • (ρ i : Measure (E × E)).map ((fun x : E => -x) ∘ Prod.snd) = γ
      simp only [h, ← Finset.sum_smul, hp, one_smul]
  · rw [push _ (by fun_prop)]
    apply Finset.sum_congr rfl
    intro i _
    have he : ((fun z : Fin 3 → E => z 0 + z 1 + z 2) ∘ T i) = fun _ => m i := by
      funext z
      change (m i + z.1 + z.2) + -z.1 + -z.2 = m i
      abel
    rw [he, Measure.map_const, measure_univ, one_smul]

#print axioms mix_pairs

/-- Independent analytic input. A positive twice continuously differentiable log-concave density relative to a standard
Gaussian, with mass one and barycentre m, is the law of m plus two standard Gaussian vectors. -/
def GaussianTiltPairs : Prop :=
  ∀ (J : Finset ℕ), J.Nonempty → ∀ (f : C(J → ℝ, ℝ)) (m : J → ℝ),
    (∀ x, 0 < f x) → ContDiff ℝ 2 (f : (J → ℝ) → ℝ) → ConcaveOn ℝ univ (fun x => Real.log (f x)) →
    (∫ x, f x ∂finiteGaussian J) = 1 →
    (∀ v : (J → ℝ) →L[ℝ] ℝ, (∫ x, f x * v x ∂finiteGaussian J) = v m) →
    ∃ ρ : ProbabilityMeasure ((J → ℝ) × (J → ℝ)),
      (ρ : Measure ((J → ℝ) × (J → ℝ))).map Prod.fst = finiteGaussian J ∧
      (ρ : Measure ((J → ℝ) × (J → ℝ))).map Prod.snd = finiteGaussian J ∧
      (ρ : Measure ((J → ℝ) × (J → ℝ))).map (fun z => m + z.1 + z.2) =
        (finiteGaussian J).withDensity (fun x => ENNReal.ofReal (f x))

private theorem density_mixture {ι V : Type*} [Fintype ι] [MeasurableSpace V] (γ : Measure V)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (f : ι → V → ℝ) (hf : ∀ i, Measurable (f i))
    (hf₀ : ∀ i x, 0 ≤ f i x) (hm : ∀ x, ∑ i, p i * f i x = 1) :
    ∑ i, ENNReal.ofReal (p i) • γ.withDensity (fun x => ENNReal.ofReal (f i x)) = γ := by
  have hone (x) : ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f i x) = 1 := by
    calc
      _ = ENNReal.ofReal (∑ i, p i * f i x) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hf₀ i x))]
        simp only [ENNReal.ofReal_mul (hp _)]
      _ = _ := by rw [hm, ENNReal.ofReal_one]
  ext1 A hA
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA]
  calc
    _ = ∫⁻ x in A, ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f i x) ∂γ := by
      rw [lintegral_finsetSum (f := fun i x => ENNReal.ofReal (p i) * ENNReal.ofReal (f i x))
        Finset.univ (fun i _ => measurable_const.mul (hf i).ennreal_ofReal)]
      simp only [lintegral_const_mul _ (hf _).ennreal_ofReal]
    _ = _ := by simp [hone]

/-- Reconstruct the finite-atomic Gaussian triple from the two-Gaussian representation
of centered log-concave Gaussian tilts. -/
theorem finite_triple_of_tilt_pairs (h : GaussianTiltPairs) (J : Finset ℕ) (hJ : J.Nonempty)
    {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    FiniteTripleDecomposition (finiteGaussian J) ((finiteGaussian J).map (fun x => r • x)) := by
  intro F hF ν hdom
  obtain ⟨s,w,hp,hp1,hν,hparts⟩ := gaussian_finite_conditionals J hF ν hr hr' hdom
  let p (i : s) := (ν : Measure F).real {i.val}
  let f (i : s) : C(J → ℝ, ℝ) := ⟨density p w i, (hparts.2 i).2.1⟩
  let τ (i : s) := (finiteGaussian J).withDensity (fun x => ENNReal.ofReal (f i x))
  have hsmooth (i : s) : ContDiff ℝ 2 (f i : (J → ℝ) → ℝ) := by
    have hrw (j : s) : ContDiff ℝ 2 (fun x => Real.exp (affineScore w j x)) :=
      (contDiff_const.add (w.2 j).contDiff).exp
    apply ContDiff.div_const
    exact (hrw i).div (ContDiff.sum fun j _ => hrw j) fun x =>
      (Finset.sum_pos (fun j _ => Real.exp_pos (affineScore w j x)) ⟨i, Finset.mem_univ _⟩).ne'
  have hρ (i : s) := h J hJ (f i) i.val.val (hparts.2 i).1 (hsmooth i) (hparts.2 i).2.2.1
    (hparts.2 i).2.2.2.1 (hparts.2 i).2.2.2.2
  choose ρ hfst hsnd ht using hρ
  have hp' : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hp i).le), hp1, ENNReal.ofReal_one]
  have hm : ∑ i, ENNReal.ofReal (p i) • τ i = finiteGaussian J :=
    density_mixture _ p (fun i => (hp i).le) (fun i => f i) (fun i => (f i).continuous.measurable)
      (fun i x => ((hparts.2 i).1 x).le) hparts.1
  obtain ⟨π, hπ, hsum⟩ := mix_pairs _ (Green54Symmetric.finite_reflection J).map_eq
    (fun i => ENNReal.ofReal (p i)) hp' (fun i : s => i.val.val) τ hm ρ hfst hsnd ht
  exact ⟨π, hπ, hsum.trans hν.symm⟩

/-- The pinned positive Green 54 statement from the two-Gaussian theorem for log-concave tilts. -/
theorem green_54_of_tilt_pairs (h : GaussianTiltPairs) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C :=
  green_54_of_finite_laws (fun J hJ _ hr hr' => finite_triple_of_tilt_pairs h J hJ hr hr')

#print axioms finite_triple_of_tilt_pairs
#print axioms green_54_of_tilt_pairs

end Green54GaussianTilts
