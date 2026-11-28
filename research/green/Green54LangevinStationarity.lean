import Green54GaussianBalance
import Green54GaussianKernel
import Green54GaussianIterations
import Green54LangevinConvergence

/-! A finite-dimensional weak error estimate for the unadjusted Langevin algorithm. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace
open scoped ENNReal
noncomputable section
namespace Green54LangevinStationarity
variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V] {P : Measure Ω} {μ : Measure V} [SFinite μ]

/-- A pointwise envelope on the simulated pair controls its one-step stationarity defect. -/
theorem simulated_balance {w : Ω → V × V} (hw : Measurable w)
    {a : V × V → ℝ} (ha : Measurable a) (hpos : ∀ z, 0 < a z)
    (hlaw : P.map w = (μ.prod μ).withDensity (fun z => ENNReal.ofReal (a z)))
    {f : V → ℝ} (hf : Measurable f)
    (hinc : Integrable (fun z => f (w z).2 - f (w z).1) P)
    {B : Ω → ℝ} (hB : Integrable B P)
    (hcost : ∀ z, |Real.log (a (w z)) - Real.log (a (w z).swap)| *
      |f (w z).2 - f (w z).1| ≤ B z) :
    |∫ z, (f (w z).2 - f (w z).1) ∂P| ≤ ∫ z, B z ∂P := by
  let D (z : V × V) := f z.2-f z.1
  let C (z : V × V) := |Real.log (a z) - Real.log (a z.swap)| * |D z|
  have hD : Measurable D := (hf.comp measurable_snd).sub (hf.comp measurable_fst)
  have hC : Measurable C := (ha.log.sub (ha.comp measurable_swap).log).abs.mul hD.abs
  have hC₀ (z : V × V) : 0 ≤ C z := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hCi : Integrable (C ∘ w) P := hB.mono' (hC.comp hw).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa only [Function.comp_apply, Real.norm_of_nonneg (hC₀ _)] using hcost z)
  have hfin : ∀ᵐ z ∂μ.prod μ, ENNReal.ofReal (a z) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have intw (g : V × V → ℝ) (hg : Measurable g) (hi : Integrable (g ∘ w) P) :
      Integrable (fun z => a z * g z) (μ.prod μ) := by
    have h := (integrable_map_measure hg.aestronglyMeasurable hw.aemeasurable).mpr hi
    rw [hlaw, integrable_withDensity_iff_integrable_smul' ha.ennreal_ofReal hfin] at h
    simpa only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul] using h
  have eqw (g : V × V → ℝ) (hg : Measurable g) :
      (∫ z, g (w z) ∂P) = ∫ z, a z * g z ∂μ.prod μ := by
    rw [← integral_map hw.aemeasurable hg.aestronglyMeasurable, hlaw,
      integral_withDensity_eq_integral_toReal_smul ha.ennreal_ofReal hfin]
    simp only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul]
  have hi := intw D hD hinc
  have hmin := ha.min (ha.comp measurable_swap)
  have hm : Integrable (fun z => min (a z) (a z.swap) * D z) (μ.prod μ) := by
    apply hi.norm.mono' (hmin.mul hD).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    change ‖min (a z) (a z.swap) * D z‖ ≤ ‖a z * D z‖
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_min (hpos _).le (hpos _).le), Real.norm_of_nonneg (hpos _).le]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
  have hb := intw C hC hCi
  have he := Green54GaussianBalance.balance_error a f hpos hi hm
    (by simpa only [C,D,mul_assoc] using hb)
  change |∫ z, D (w z) ∂P| ≤ _
  rw [eqw D hD]
  apply he.trans
  calc
    _ = ∫ z, C (w z) ∂P := by rw [eqw C hC]; simp only [C,D,mul_assoc]
    _ ≤ _ := integral_mono hCi hB hcost
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Euler proposal with a standard Gaussian innovation. -/
def proposal (G : E → E) (h : ℝ) (x z : E) := x-h • G x + Real.sqrt (2*h) • z

/-- The Markov operator of one additive Gaussian step. -/
def transition (D : E → E) (σ : ℝ) (f : E → ℝ) (x : E) :=
  ∫ z, f (D x + σ • z) ∂stdGaussian E

private theorem innovation_integrable {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f)
    (m : E) (σ : ℝ) : Integrable (fun z => f (m + σ • z)) (stdGaussian E) := by
  have hn : Integrable (fun z : E => ‖z‖) (stdGaussian E) :=
    IsGaussian.memLp_two_id.norm.integrable (by norm_num)
  apply ((integrable_const ‖f m‖).add (hn.const_mul ((K:ℝ)*‖σ‖))).mono'
    (hf.continuous.measurable.comp (by fun_prop : Measurable (fun z : E => m+σ • z))).aestronglyMeasurable
  apply ae_of_all
  intro z
  have he := hf.norm_sub_le (m+σ • z) m
  rw [add_sub_cancel_left, norm_smul] at he
  change ‖f (m+σ • z)‖ ≤ ‖f m‖ + _*‖z‖
  nlinarith [norm_sub_norm_le (f (m+σ • z)) (f m)]

/-- A common Gaussian innovation preserves the deterministic contraction factor. -/
theorem transition_lipschitz {D : E → E} {r : NNReal} (hD : LipschitzWith r D) (σ : ℝ)
    {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) :
    LipschitzWith (r*K) (transition D σ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  unfold transition
  rw [← integral_sub (innovation_integrable hf _ _) (innovation_integrable hf _ _)]
  have hb (z : E) : ‖f (D x + σ • z)-f (D y + σ • z)‖ ≤ (r*K:NNReal)*‖x-y‖ := by
    apply (hf.norm_sub_le _ _).trans
    rw [add_sub_add_right_eq_sub]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (hD.norm_sub_le x y) K.coe_nonneg]
  simpa using norm_integral_le_of_norm_le (integrable_const (μ := stdGaussian E) ((r*K:NNReal)*‖x-y‖ : ℝ))
    (ae_of_all _ hb)

private def pairDensity (U : E → ℝ) (G : E → E) (c h : ℝ) (s : E × E) :=
  c * Real.exp (-U s.1) *
    Green54GaussianKernel.gaussianDensity (s.1-h • G s.1) (Real.toNNReal (2*h)) s.2

private theorem pair_law {U : E → ℝ} (hU : Measurable U) {G : E → E} (hG : Measurable G)
    (c : ℝ) (hc : 0 < c) {h : ℝ} (hh : 0 < h) :
    let π := (volume : Measure E).withDensity (fun x => ENNReal.ofReal (c*Real.exp (-U x)))
    (π.prod (stdGaussian E)).map (fun s : E × E => (s.1,proposal G h s.1 s.2)) =
      ((volume : Measure E).prod volume).withDensity (fun s => ENNReal.ofReal (pairDensity U G c h s)) := by
  let v := Real.toNNReal (2*h)
  have hvar : (⟨Real.sqrt (2*h)^2, sq_nonneg _⟩ : ℝ≥0) = v := by
    apply NNReal.eq
    change Real.sqrt (2*h)^2 = (Real.toNNReal (2*h) : ℝ)
    rw [Real.sq_sqrt (by positivity), Real.coe_toNNReal _ (by positivity)]
  have hstep (x : E) := Green54GaussianKernel.affine_gaussian_density (x-h • G x)
    (Real.sqrt (2*h)) (Real.sqrt_pos.mpr (by positivity)).ne'
  let q (s : E × E) := ENNReal.ofReal (Green54GaussianKernel.gaussianDensity (s.1-h • G s.1) v s.2)
  have hq : Measurable q := by unfold q Green54GaussianKernel.gaussianDensity; fun_prop
  have hp : Measurable (fun x : E => ENNReal.ofReal (c*Real.exp (-U x))) := by fun_prop
  have hpr : Measurable (Function.uncurry (proposal G h)) := by unfold Function.uncurry proposal; fun_prop
  have hj := Green54GaussianKernel.weighted_joint volume (stdGaussian E) hp hq hpr
    (fun x => by unfold proposal; simpa only [q,hvar] using hstep x)
  convert hj using 3
  exact ENNReal.ofReal_mul (mul_nonneg hc.le (Real.exp_pos _).le)

private theorem pair_pos {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (U : E → ℝ) (G : E → E) (s : E × E) :
    0 < pairDensity U G c h s := by
  unfold pairDensity Green54GaussianKernel.gaussianDensity
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2*h)]
  positivity

private theorem pair_log {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (U : E → ℝ) (G : E → E) (s : E × E) :
    Real.log (pairDensity U G c h s) =
      (Real.log c + Real.log ((Real.sqrt (2*Real.pi*(2*h)))⁻¹ ^ Fintype.card ι)) +
      (-U s.1 - ‖(s.2-s.1)+h • G s.1‖^2/(4*h)) := by
  unfold pairDensity Green54GaussianKernel.gaussianDensity
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2*h)]
  have hconst : 0 < (Real.sqrt (2*Real.pi*(2*h)))⁻¹ ^ Fintype.card ι := by positivity
  rw [Real.log_mul (mul_pos hc (Real.exp_pos _)).ne' (mul_pos hconst (Real.exp_pos _)).ne',
    Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_mul hconst.ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_exp]
  rw [show s.2-(s.1-h • G s.1) = (s.2-s.1)+h • G s.1 by abel,show 2*(2*h)=4*h by ring]
  ring
/-- The change of a Lipschitz observable after one Euler step is controlled by the
cubic moment of the drift and innovation. The moment is taken at the target law. -/
theorem one_step_error {U : E → ℝ} (hU : Measurable U) {G : E → E} {L : NNReal}
    (hG : LipschitzWith L G) (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x)
    {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1)
    {π : Measure E} [IsProbabilityMeasure π]
    (hπ : π = volume.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-U x))))
    (hM : Integrable (fun s : E × E => (‖G s.1‖+2*‖s.2‖)^3) (π.prod (stdGaussian E)))
    {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) :
    |∫ x, transition (fun y => y-h • G y) (Real.sqrt (2*h)) f x - f x ∂π| ≤
      (K:ℝ)*((L:ℝ)/2+L/4*(2+L))*(Real.sqrt h)^3 *
        ∫ s : E × E, (‖G s.1‖+2*‖s.2‖)^3 ∂π.prod (stdGaussian E) := by
  let P := π.prod (stdGaussian E)
  let w (s : E × E) := (s.1,proposal G h s.1 s.2)
  let B (s : E × E) := ‖G s.1‖+2*‖s.2‖
  let A := (K:ℝ)*((L:ℝ)/2+L/4*(2+L))*(Real.sqrt h)^3
  have hmG := hG.continuous.measurable
  have hw : Measurable w := by unfold w proposal; fun_prop
  have ha : Measurable (pairDensity U G c h) := by
    unfold pairDensity Green54GaussianKernel.gaussianDensity; fun_prop
  have hlaw : P.map w = ((volume : Measure E).prod volume).withDensity (fun s => ENNReal.ofReal (pairDensity U G c h s)) := by unfold P w; rw [hπ]; exact pair_law hU hmG c hc hh
  have hB₀ (s : E × E) : 0 ≤ B s := by unfold B; positivity
  have hσ : Real.sqrt (2*h) ≤ 2 := by
    apply (Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩)
  have hd (s : E × E) : ‖(w s).2-(w s).1‖ ≤ B s := by
    change ‖s.1 - h • G s.1 + Real.sqrt (2*h) • s.2 - s.1‖ ≤ _
    rw [show s.1 - h • G s.1 + Real.sqrt (2*h) • s.2 - s.1 =
      -(h • G s.1) + Real.sqrt (2*h) • s.2 by abel]
    apply (norm_add_le _ _).trans
    rw [norm_neg,norm_smul,norm_smul,Real.norm_of_nonneg hh.le,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    unfold B
    nlinarith [mul_le_mul_of_nonneg_right hh1 (norm_nonneg (G s.1)),mul_le_mul_of_nonneg_right hσ (norm_nonneg s.2)]
  have hi : Integrable (fun s => f (w s).2-f (w s).1) P := by
    apply (((integrable_const (μ := P) (1:ℝ)).add hM).const_mul (K:ℝ)).mono'
      ((hf.continuous.measurable.comp (measurable_snd.comp hw)).sub
        (hf.continuous.measurable.comp (measurable_fst.comp hw))).aestronglyMeasurable
    apply ae_of_all
    intro s
    change ‖f (w s).2 - f (w s).1‖ ≤ (K:ℝ)*(1+(B s)^3)
    apply (hf.norm_sub_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    apply (hd s).trans
    rcases le_total (B s) 1 with he | he
    · linarith [pow_nonneg (hB₀ s) 3]
    · nlinarith [mul_le_mul_of_nonneg_right he (hB₀ s),
        mul_le_mul_of_nonneg_right he (sq_nonneg (B s))]
  have hb : Integrable (fun s => A*(B s)^3) P := hM.const_mul A
  have hdiff : (∫ x, transition (fun y => y-h • G y) (Real.sqrt (2*h)) f x - f x ∂π) =
      ∫ s, f (w s).2-f (w s).1 ∂P := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change _ = ∫ z, f (x-h • G x+Real.sqrt (2*h) • z)-f x ∂stdGaussian E
    rw [integral_sub (innovation_integrable hf _ _) (integrable_const _)]
    simp [transition]
  rw [hdiff]
  change |∫ s, f (w s).2-f (w s).1 ∂P| ≤ A * ∫ s, (B s)^3 ∂P
  rw [← integral_const_mul]
  apply simulated_balance hw ha (pair_pos hc hh U G) hlaw hf.continuous.measurable hi hb
  intro s
  rcases s with ⟨x,z⟩
  let y := proposal G h x z
  change |Real.log (pairDensity U G c h (x,y))-Real.log (pairDensity U G c h (y,x))| * |f y-f x| ≤ _
  rw [pair_log hc hh,pair_log hc hh,add_sub_add_left_eq_sub]
  have hf' : |f y-f x| ≤ (K:ℝ)*‖y-x‖ := hf.norm_sub_le _ _
  apply (mul_le_mul_of_nonneg_left hf' (abs_nonneg _)).trans
  have he := mul_le_mul_of_nonneg_left (Green54GaussianBalance.proposal_cubic_error hG hsub hh hh1 x z) K.coe_nonneg
  change _ ≤ A*(‖G x‖+2*‖z‖)^3
  dsimp only [Prod.fst,Prod.snd]
  unfold A
  let φ (a b : E) := -U a - ‖(b-a)+h • G a‖^2/(4*h)
  change (K:ℝ)*(‖y-x‖*|φ x y-φ y x|) ≤ (K:ℝ)*(((L:ℝ)/2+L/4*(2+L))*(Real.sqrt h)^3*(‖G x‖+2*‖z‖)^3) at he
  change |φ x y-φ y x| *((K:ℝ)*‖y-x‖) ≤ _
  calc
    _ = (K:ℝ)*(‖y-x‖*|φ x y-φ y x|) := by ring
    _ ≤ _ := he.trans_eq (by ring)


/-- Explicit weak error from a deterministic seed for any Lipschitz observable.
The transient decays geometrically and the remaining error is of order √h. -/
theorem endpoint_error {U : E → ℝ} (hU : Measurable U) {G : E → E} {L : NNReal}
    (hG : LipschitzWith L G) (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x)
    (hmon : ∀ x y, ‖x-y‖^2 ≤ ⟪x-y,G x-G y⟫) {c h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hsmall : 2*h ≤ 1) (hgrad : h*(L:ℝ)^2 ≤ 1) {π : Measure E} [IsProbabilityMeasure π]
    (hπ : π = volume.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-U x))))
    (hM : Integrable (fun s : E × E => (‖G s.1‖+2*‖s.2‖)^3) (π.prod (stdGaussian E)))
    (x₀ : E) (h₀ : Integrable (dist x₀) π) {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) (n : ℕ) :
    |(transition (fun y => y-h • G y) (Real.sqrt (2*h)))^[n] f x₀ - ∫ x, f x ∂π| ≤
      (K:ℝ)*(Real.sqrt (1-h)^n*(∫ x, dist x₀ x ∂π) +
        2*((L:ℝ)/2+L/4*(2+L))*Real.sqrt h *
          (∫ s : E × E, (‖G s.1‖+2*‖s.2‖)^3 ∂π.prod (stdGaussian E))) := by
  let r : NNReal := ⟨Real.sqrt (1-h),Real.sqrt_nonneg _⟩
  let D (x : E) := x - h • G x
  let σ := Real.sqrt (2*h)
  let M := ∫ s : E × E, (‖G s.1‖+2*‖s.2‖)^3 ∂π.prod (stdGaussian E)
  let C := (L:ℝ)/2+L/4*(2+L)
  have hM₀ : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hC : 0 ≤ C := by unfold C; positivity
  have hr2 : (r:ℝ)^2=1-h := Real.sq_sqrt (by linarith)
  have hr : (r:ℝ)<1 := by nlinarith [r.coe_nonneg]
  have hD : LipschitzWith r D := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg r.coe_nonneg (norm_nonneg _))).mp
    rw [mul_pow,hr2]
    exact (Green54GaussianIterations.gradient_step_sq hG hmon hh.le x y).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hgrad hh.le]) (sq_nonneg _))
  have hE := Green54LangevinConvergence.endpoint_bias π x₀ h₀ (transition D σ) hr
    (δ := C*(Real.sqrt h)^3*M) (by positivity)
    (fun hg => transition_lipschitz hD σ hg) (fun {k g} hg => by
      have hz := one_step_error hU hG hsub hc hh (by linarith) hπ hM hg
      change _ ≤ C*(Real.sqrt h)^3*M*(k:ℝ)
      exact hz.trans_eq (by unfold C M; ring)) hf n
  apply hE.trans
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  apply add_le_add le_rfl
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  have hden : h ≤ 2*(1-(r:ℝ)) := by nlinarith [sq_nonneg (1-(r:ℝ))]
  have he := mul_le_mul_of_nonneg_left hden (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg h)) hM₀)
  have hcub : Real.sqrt h ^ 3 = Real.sqrt h * h := by
    rw [pow_succ,Real.sq_sqrt hh.le,mul_comm]
  rw [hcub]
  change C*(Real.sqrt h*h)*M ≤ 2*C*Real.sqrt h*M*(1-(r:ℝ))
  nlinarith only [he]

/-- One step size and iteration count work simultaneously for every Lipschitz test.
This includes the unbounded linear tests used for the barycentre. -/
theorem approximate_target {U : E → ℝ} (hU : Measurable U) {G : E → E} {L : NNReal}
    (hG : LipschitzWith L G) (hsub : ∀ x y, ⟪G x,y-x⟫ ≤ U y-U x)
    (hmon : ∀ x y, ‖x-y‖^2 ≤ ⟪x-y,G x-G y⟫) {c : ℝ} (hc : 0 < c)
    {π : Measure E} [IsProbabilityMeasure π]
    (hπ : π = volume.withDensity (fun x => ENNReal.ofReal (c*Real.exp (-U x))))
    (hM : Integrable (fun s : E × E => (‖G s.1‖+2*‖s.2‖)^3) (π.prod (stdGaussian E)))
    (x₀ : E) (h₀ : Integrable (dist x₀) π) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ 2*h ≤ 1 ∧ h*(L:ℝ)^2 ≤ 1 ∧ ∃ n : ℕ, ∀ {K : NNReal} {f : E → ℝ},
      LipschitzWith K f → |(transition (fun y => y-h • G y) (Real.sqrt (2*h)))^[n] f x₀ -
        ∫ x, f x ∂π| ≤ (K:ℝ)*ε := by
  let M := ∫ s : E × E, (‖G s.1‖+2*‖s.2‖)^3 ∂π.prod (stdGaussian E)
  let A := 2*((L:ℝ)/2+L/4*(2+L))*M
  have hM₀ : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hA : 0 ≤ A := by unfold A; positivity
  let t := ε/(2*(A+1))
  have ht : 0 < t := by unfold t; positivity
  let h := min (min (1/2:ℝ) (1/((L:ℝ)^2+1))) (t^2)
  have hh : 0 < h := by unfold h; positivity
  have hs : 2*h ≤ 1 := by linarith [(min_le_left _ _ : h ≤ min (1/2:ℝ) (1/((L:ℝ)^2+1))).trans (min_le_left _ _)]
  have hL := (min_le_left _ _ : h ≤ min (1/2:ℝ) (1/((L:ℝ)^2+1))).trans (min_le_right _ _)
  have hgrad : h*(L:ℝ)^2 ≤ 1 := by
    have h' := (le_div_iff₀ (by positivity : 0 < (L:ℝ)^2+1)).mp hL
    nlinarith
  have hroot : Real.sqrt h ≤ t := Real.sqrt_le_iff.mpr ⟨ht.le,min_le_right _ _⟩
  have he : A * Real.sqrt h ≤ ε/2 := by
    have ht' : t*(2*(A+1))=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hroot hA]
  let r := Real.sqrt (1-h)
  have hr : r<1 := by unfold r; apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr; linarith
  have htend := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg (1-h)) hr).mul_const
    (∫ x, dist x₀ x ∂π)
  rw [zero_mul] at htend
  obtain ⟨n,hn⟩ := (htend.eventually_lt_const (half_pos hε)).exists
  refine ⟨h,hh,hs,hgrad,n,?_⟩
  intro K f hf
  apply (endpoint_error hU hG hsub hmon hc hh hs hgrad hπ hM x₀ h₀ hf n).trans
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  change Real.sqrt (1-h)^n*(∫ x, dist x₀ x ∂π)+2*((L:ℝ)/2+L/4*(2+L))*Real.sqrt h*M ≤ ε
  change Real.sqrt (1-h)^n*(∫ x, dist x₀ x ∂π)<ε/2 at hn
  unfold A at he
  linarith

#print axioms endpoint_error
#print axioms approximate_target
#print axioms simulated_balance
#print axioms transition_lipschitz
#print axioms one_step_error
end Green54LangevinStationarity
