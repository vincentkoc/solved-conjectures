import Green54GaussianTilts
import Green54GaussianContractions

/-! The Lipschitz approximation and contractive transport inputs in the Gaussian tilt theorem. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal Pointwise
open Green54Contractions Green54ConvexTests Green54Projections Green54GaussianTilts

namespace Green54ContractionReduction

/-- The discrete approximation in the Lipschitz image lemma, normalized to Lipschitz bound two.
The coordinates of the Bochner barycentre are written as scalar integrals. -/
def LipschitzApproximation : Prop :=
  ∀ (J : Finset ℕ) (T : EuclideanSpace ℝ J → EuclideanSpace ℝ J), LipschitzWith 2 T →
    let γ := stdGaussian (EuclideanSpace ℝ J)
    let m := WithLp.toLp 2 fun i => ∫ x, T x i ∂γ
    ∃ ν ∈ closure (adaptedLaws J), (ν : Measure (EuclideanSpace ℝ J)) =
      γ.map (fun x => (2 : ℝ)⁻¹ • (T x - m))

/-- Caffarelli's contraction theorem in the chart of the finite Gaussian used in Green 54. -/
def ContractiveTransport : Prop :=
  ∀ (J : Finset ℕ), J.Nonempty → ∀ (f : C(J → ℝ, ℝ)),
    (∀ x, 0 < f x) → ContDiff ℝ 2 (f : (J → ℝ) → ℝ) →
    ConcaveOn ℝ univ (fun x => Real.log (f x)) → (∫ x, f x ∂finiteGaussian J) = 1 →
    ∃ T : EuclideanSpace ℝ J → EuclideanSpace ℝ J, LipschitzWith 1 T ∧
      (stdGaussian (EuclideanSpace ℝ J)).map (fun x => (T x).ofLp) =
        (finiteGaussian J).withDensity (fun x => ENNReal.ofReal (f x))

private theorem ofLp_standard (J : Finset ℕ) :
    (stdGaussian (EuclideanSpace ℝ J)).map WithLp.ofLp = finiteGaussian J := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (PiLp.continuous_ofLp 2 _).measurable (PiLp.continuous_toLp 2 _).measurable]
  exact Measure.map_id

/-- The finite approximation theorem and contractive transport together yield the exact
pair representation for all smooth log-concave Gaussian tilts used by the softmax proof. -/
theorem tilt_pairs_of_approximation_and_transport
    (ha : LipschitzApproximation) (ht : ContractiveTransport) : GaussianTiltPairs := by
  intro J hJ f m hf hc hl hm hbar
  let E := EuclideanSpace ℝ J
  let γ := stdGaussian E
  obtain ⟨T, hT, hτ⟩ := ht J hJ f hf hc hl hm
  have hTm : Measurable T := hT.continuous.measurable
  have hdown : Continuous (WithLp.ofLp : E → (J → ℝ)) := PiLp.continuous_ofLp 2 _
  have hY : Measurable (fun x => (T x).ofLp) := (hdown.comp hT.continuous).measurable
  have hmean (i : J) : (∫ x, T x i ∂γ) = m i := by
    let v : (J → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    calc
      _ = ∫ x, v x ∂(γ.map (fun x => (T x).ofLp)) :=
        (integral_map hY.aemeasurable v.continuous.aestronglyMeasurable).symm
      _ = ∫ x, f x * v x ∂finiteGaussian J := by
        rw [hτ, integral_withDensity_eq_integral_toReal_smul f.continuous.measurable.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
        simp only [ENNReal.toReal_ofReal (hf _).le, smul_eq_mul]
      _ = m i := hbar v
  obtain ⟨ν, hν, hhalf⟩ := ha J T (hT.weaken (by norm_num))
  obtain ⟨ρ, h₁, h₂, hout⟩ := closure_adaptedLaws_subset hν
  let p (z : E × E) := (z.1.ofLp, z.2.ofLp)
  have hp : Measurable p := (hdown.comp continuous_fst).measurable.prodMk
    (hdown.comp continuous_snd).measurable
  let σ := ρ.map hp.aemeasurable
  refine ⟨σ, ?_, ?_, ?_⟩
  · change ((ρ : Measure (E × E)).map p).map Prod.fst = _
    rw [Measure.map_map measurable_fst hp]
    exact ((Measure.map_map hdown.measurable measurable_fst).symm.trans
      (congrArg (Measure.map WithLp.ofLp) h₁)).trans (ofLp_standard J)
  · change ((ρ : Measure (E × E)).map p).map Prod.snd = _
    rw [Measure.map_map measurable_snd hp]
    exact ((Measure.map_map hdown.measurable measurable_snd).symm.trans
      (congrArg (Measure.map WithLp.ofLp) h₂)).trans (ofLp_standard J)
  · let mid (z : E × E) := (2 : ℝ)⁻¹ • (z.1 + z.2)
    let rescale (z : E) := m + (2 : ℝ) • z.ofLp
    have hr : Measurable rescale := by
      unfold rescale
      exact (continuous_const.add (hdown.const_smul (2 : ℝ))).measurable
    have hcMid : Measurable mid := by unfold mid; fun_prop
    have he : (fun z : (J → ℝ) × (J → ℝ) => m + z.1 + z.2) ∘ p = rescale ∘ mid := by
      funext z i
      change m i + z.1 i + z.2 i = m i + 2 * ((2 : ℝ)⁻¹ * (z.1 i + z.2 i))
      ring
    change ((ρ : Measure (E × E)).map p).map _ = _
    rw [Measure.map_map (by fun_prop) hp, he, ← Measure.map_map hr hcMid, hout, hhalf,
      Measure.map_map hr (by fun_prop), ← hτ]
    congr 1
    funext x i
    change m i + 2 * ((2 : ℝ)⁻¹ * (T x i - ∫ y, T y i ∂γ)) = T x i
    rw [hmean]
    ring

/-- The two analytic inputs imply the pinned positive Green 54 declaration. -/
theorem green_54_of_approximation_and_transport
    (ha : LipschitzApproximation) (ht : ContractiveTransport) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤ gaussian K →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
      (0.01 : ℝ≥0∞) ≤ gaussian C :=
  green_54_of_tilt_pairs (tilt_pairs_of_approximation_and_transport ha ht)

#print axioms tilt_pairs_of_approximation_and_transport
#print axioms green_54_of_approximation_and_transport
end Green54ContractionReduction
