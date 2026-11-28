import Green54LangevinStationarity
/-! Gaussian product coordinates and expectations of finite Langevin paths. -/

open MeasureTheory ProbabilityTheory Set Green54GaussianIterations
open scoped NNReal ENNReal
noncomputable section
namespace Green54LangevinPaths
variable {ι J : Type*} [Fintype ι] [Fintype J]
local notation "E" => EuclideanSpace ℝ ι

private theorem flatten_coordinates :
    MeasurePreserving (fun (x : J → E) (s : J × ι) => x s.1 s.2)
      (Measure.pi fun _ => stdGaussian E) (Measure.pi fun _ => gaussianReal 0 1) := by
  let F (x : J → E) (s : J × ι) := x s.1 s.2
  have hF : Measurable F := by unfold F; fun_prop
  refine ⟨hF,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hF (MeasurableSet.univ_pi hs)]
  let R (j : J) := (WithLp.ofLp : E → ι → ℝ) ⁻¹' (univ.pi fun i => s (j,i))
  have he : F ⁻¹' (univ.pi s) = univ.pi R := by
    ext x
    simp only [Set.mem_preimage,Set.mem_univ_pi,R,F]
    exact ⟨fun h j i => h (j,i),fun h z => h z.1 z.2⟩
  change (Measure.pi fun _ : J => stdGaussian E) (F ⁻¹' (univ.pi s)) = _
  rw [he,Measure.pi_pi,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [← map_pi_eq_stdGaussian]
  change ((Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2)) _ = _
  rw [Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
    ((MeasurableSet.univ_pi fun i => hs (j,i)).preimage (PiLp.continuous_ofLp 2 _).measurable)]
  exact Measure.pi_pi _ _

/-- Splitting a standard Gaussian into coordinate blocks gives independent standard Gaussians. -/
theorem block_preserving (n : ℕ) :
    MeasurePreserving (block (ι := ι) (n := n)) (stdGaussian (EuclideanSpace ℝ (Fin n × ι)))
      (Measure.pi fun _ => stdGaussian E) := by
  let F (x : Fin n → E) := WithLp.toLp 2 (fun p : Fin n × ι => x p.1 p.2)
  have hF : MeasurePreserving F (Measure.pi fun _ => stdGaussian E) (stdGaussian _) :=
    (show MeasurePreserving (WithLp.toLp 2) (Measure.pi fun _ : Fin n × ι => gaussianReal 0 1)
      (stdGaussian _) from ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩).comp
      flatten_coordinates
  have hB : Measurable (block (ι := ι) (n := n)) := by unfold block; fun_prop
  refine ⟨hB,?_⟩
  rw [← hF.map_eq, Measure.map_map hB hF.measurable]
  exact Measure.map_id
open Green54LangevinStationarity
private theorem chain_measurable {D : E → E} (hD : Measurable D) (σ : ℝ) (x₀ : E) (n : ℕ) :
    Measurable (chain D σ x₀ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (hD.comp (ih.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)))).add
      ((measurable_const (a := σ)).smul (measurable_pi_apply (Fin.last n)))

private theorem gaussian_test {κ : Type*} [Fintype κ] {K : NNReal} {f : EuclideanSpace ℝ κ → ℝ}
    (hf : LipschitzWith K f) : Integrable f (stdGaussian _) := by
  have hn : Integrable (fun z : EuclideanSpace ℝ κ => ‖z‖) (stdGaussian _) :=
    IsGaussian.memLp_two_id.norm.integrable (by norm_num)
  apply ((integrable_const ‖f 0‖).add (hn.const_mul (K:ℝ))).mono' hf.continuous.aestronglyMeasurable
  apply ae_of_all
  intro z
  have he := hf.norm_sub_le z 0
  rw [sub_zero] at he
  change ‖f z‖ ≤ ‖f 0‖+(K:ℝ)*‖z‖
  linarith [norm_sub_norm_le (f z) (f 0)]

private theorem chain_integrable {D : E → E} {r : NNReal} (hD : LipschitzWith r D) {σ : ℝ}
    (hσ : 0 ≤ σ) (hs : (r:ℝ)^2+σ^2/4 ≤ 1) (x₀ : E) (n : ℕ) {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) : Integrable (fun z => f (chain D σ x₀ n z))
      (Measure.pi fun _ => stdGaussian E) := by
  have he := hf.comp (chain_lipschitz hσ (fun x y => hD.norm_sub_le x y) hs x₀ n)
  apply ((block_preserving n).integrable_comp
    (hf.continuous.measurable.comp (chain_measurable hD.continuous.measurable σ x₀ n)).aestronglyMeasurable).mp
  exact gaussian_test he

/-- Expectations of a finite Gaussian path endpoint coincide with iterates of the transition
operator, including for unbounded Lipschitz tests. -/
theorem chain_integral {D : E → E} {r : NNReal} (hD : LipschitzWith r D) {σ : ℝ}
    (hσ : 0 ≤ σ) (hs : (r:ℝ)^2+σ^2/4 ≤ 1) (x₀ : E) (n : ℕ) {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) : (∫ z, f (chain D σ x₀ n z) ∂Measure.pi (fun _ => stdGaussian E)) =
      (transition D σ)^[n] f x₀ := by
  induction n generalizing K f with
  | zero => simp [chain]
  | succ n ih =>
    let μ := Measure.pi (fun _ : Fin n => stdGaussian E)
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).trans MeasurableEquiv.prodComm
    have hpres : MeasurePreserving e (Measure.pi (fun _ => stdGaussian E)) (μ.prod (stdGaussian E)) :=
      Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => stdGaussian E) (Fin.last n))
    let F (s : (Fin n → E) × E) := f (D (chain D σ x₀ n s.1)+σ • s.2)
    have hm : Measurable F := hf.continuous.measurable.comp
      ((hD.continuous.measurable.comp ((chain_measurable hD.continuous.measurable σ x₀ n).comp measurable_fst)).add
        ((measurable_const (a := σ)).smul measurable_snd))
    have he (x : Fin (n+1) → E) : F (e x) = f (chain D σ x₀ (n+1) x) := by
      change f (D (chain D σ x₀ n (fun j => x ((Fin.last n).succAbove j)))+σ • x (Fin.last n)) = _
      simp only [Fin.succAbove_last_apply,chain]
    have hi : Integrable F (μ.prod (stdGaussian E)) := (hpres.integrable_comp hm.aestronglyMeasurable).mp
      (by simpa only [Function.comp_def,he] using chain_integrable hD hσ hs x₀ (n+1) hf)
    calc
      _ = ∫ s, F s ∂μ.prod (stdGaussian E) := by rw [← hpres.integral_comp' F]; simp only [he]
      _ = ∫ z, transition D σ f (chain D σ x₀ n z) ∂μ := integral_prod F hi
      _ = _ := by rw [ih (transition_lipschitz hD σ hf), Function.iterate_succ_apply]

/-- The same identity on the Euclidean innovation space used by the representation theorem. -/
theorem gaussian_chain_integral {D : E → E} {r : NNReal} (hD : LipschitzWith r D) {σ : ℝ}
    (hσ : 0 ≤ σ) (hs : (r:ℝ)^2+σ^2/4 ≤ 1) (x₀ : E) (n : ℕ) {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) :
    (∫ x, f (chain D σ x₀ n (block x)) ∂stdGaussian (EuclideanSpace ℝ (Fin n × ι))) =
      (transition D σ)^[n] f x₀ := by
  have hp := block_preserving (ι := ι) n
  have hm := hf.continuous.measurable.comp (chain_measurable hD.continuous.measurable σ x₀ n)
  have h := integral_map (μ := stdGaussian (EuclideanSpace ℝ (Fin n × ι))) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm.trans (chain_integral hD hσ hs x₀ n hf)

#print axioms gaussian_chain_integral
#print axioms block_preserving
#print axioms chain_integral
end Green54LangevinPaths
