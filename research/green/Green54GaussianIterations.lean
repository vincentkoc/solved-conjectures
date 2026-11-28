import Green54RectangularImages

/-! Gaussian representations for noisy iterations with a contractive deterministic step. -/

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable section
namespace Green54GaussianIterations
private theorem step_energy {D : E → E} (r σ : ℝ) (hs : 0 ≤ σ)
    (hD : ∀ x y, ‖D x-D y‖ ≤ r * ‖x-y‖) (h : r^2 + σ^2 / 4 ≤ 1)
    (x y u v : E) :
    ‖(D x+σ • u)-(D y+σ • v)‖^2 ≤ ‖x-y‖^2 + 4*‖u-v‖^2 := by
  have he : (D x+σ • u)-(D y+σ • v) = (D x-D y)+σ • (u-v) := by rw [smul_sub]; abel
  rw [he]
  have htri := norm_add_le (D x-D y) (σ • (u-v))
  rw [norm_smul, Real.norm_of_nonneg hs] at htri
  have hbound := htri.trans (add_le_add (hD x y) le_rfl)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hnon : 0 ≤ ‖x-y‖^2 + 4*‖u-v‖^2 := by positivity
  nlinarith [sq_nonneg (σ / 2 * ‖x-y‖ - 2*r*‖u-v‖),
    mul_le_mul_of_nonneg_right h hnon]
/-- Iterate the deterministic map with one fresh scaled innovation per step. -/
def chain (D : E → E) (σ : ℝ) (x₀ : E) : (n : ℕ) → (Fin n → E) → E
  | 0, _ => x₀
  | n+1, x => D (chain D σ x₀ n (fun i => x i.castSucc)) + σ • x (Fin.last n)

private theorem chain_energy {D : E → E} {r σ : ℝ} (hs : 0 ≤ σ) (hD : ∀ x y, ‖D x-D y‖ ≤ r * ‖x-y‖)
    (h : r^2+σ^2/4 ≤ 1) (x₀ : E) (n : ℕ) (u v : Fin n → E) :
    ‖chain D σ x₀ n u-chain D σ x₀ n v‖^2 ≤ 4*∑ i, ‖u i-v i‖^2 := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, mul_add]
    exact (step_energy r σ hs hD h _ _ _ _).trans
      (add_le_add (ih (fun i => u i.castSucc) (fun i => v i.castSucc)) le_rfl)

open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

/-- The coordinates of the j-th innovation in a single Euclidean product sample. -/
def block {n : ℕ} (x : EuclideanSpace ℝ (Fin n × ι)) (j : Fin n) : V :=
  WithLp.toLp 2 (fun i => x (j,i))

private theorem block_energy {n : ℕ} (x y : EuclideanSpace ℝ (Fin n × ι)) :
    (∑ j, ‖block x j - block y j‖^2) = ‖x-y‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- The endpoint is 2-Lipschitz jointly in all Gaussian innovations. -/
theorem chain_lipschitz {D : V → V} {r σ : ℝ} (hs : 0 ≤ σ) (hD : ∀ x y, ‖D x-D y‖ ≤ r * ‖x-y‖)
    (h : r^2+σ^2/4 ≤ 1) (x₀ : V) (n : ℕ) :
    LipschitzWith 2 (fun x : EuclideanSpace ℝ (Fin n × ι) => chain D σ x₀ n (block x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  have hh := chain_energy hs hD h x₀ n (block x) (block y)
  rw [block_energy] at hh
  nlinarith [norm_nonneg (chain D σ x₀ n (block x)-chain D σ x₀ n (block y)), norm_nonneg (x-y)]

/-- For a 1-strongly monotone L-Lipschitz drift, the unadjusted deterministic step contracts. -/
theorem gradient_step_sq {B : E → E} {L : NNReal} (hL : LipschitzWith L B)
    (hmon : ∀ x y, ‖x-y‖^2 ≤ ⟪x-y,B x-B y⟫) {h : ℝ} (hh : 0 ≤ h) (x y : E) :
    ‖(x-h • B x)-(y-h • B y)‖^2 ≤ (1-2*h+h^2*(L:ℝ)^2)*‖x-y‖^2 := by
  have he : (x-h • B x)-(y-h • B y) = (x-y)-h • (B x-B y) := by rw [smul_sub]; abel
  rw [he, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hl := pow_le_pow_left₀ (norm_nonneg _) (hL.norm_sub_le x y) 2
  rw [mul_pow] at hl
  nlinarith [mul_le_mul_of_nonneg_left (hmon x y) hh, mul_le_mul_of_nonneg_left hl (sq_nonneg h)]

/-- The Lipschitz image lemma gives an exact Gaussian sum law for every finite
iteration that satisfies the squared contraction condition. -/
theorem centered_chain_sum {D : V → V} {r σ : ℝ} (hs : 0 ≤ σ)
    (hD : ∀ x y, ‖D x - D y‖ ≤ r * ‖x-y‖) (h : r^2+σ^2/4 ≤ 1) (x₀ : V) (n : ℕ) :
    let f (x : EuclideanSpace ℝ (Fin n × ι)) := chain D σ x₀ n (block x)
    ∃ ρ : ProbabilityMeasure (V × V), (ρ : Measure (V × V)).map Prod.fst = stdGaussian V ∧
      (ρ : Measure (V × V)).map Prod.snd = stdGaussian V ∧
      (ρ : Measure (V × V)).map (fun z => z.1 + z.2) =
        (stdGaussian _).map (fun x => f x - ∫ z, f z ∂stdGaussian _) :=
  Green54RectangularImages.rectangular_sum (chain_lipschitz hs hD h x₀ n)

/-- A small Euler step for a one-strongly monotone Lipschitz drift meets the
two-Gaussian criterion at every finite iteration count. -/
theorem langevin_sum {G : V → V} {L : NNReal} (hL : LipschitzWith L G)
    (hmon : ∀ x y, ‖x-y‖^2 ≤ ⟪x-y,G x-G y⟫) {h : ℝ} (hh : 0 ≤ h)
    (hsmall : 2*h ≤ 1) (hgrad : h * (L : ℝ)^2 ≤ 1) (x₀ : V) (n : ℕ) :
    let f (x : EuclideanSpace ℝ (Fin n × ι)) :=
      chain (fun v => v-h • G v) (Real.sqrt (2*h)) x₀ n (block x)
    ∃ ρ : ProbabilityMeasure (V × V), (ρ : Measure (V × V)).map Prod.fst = stdGaussian V ∧
      (ρ : Measure (V × V)).map Prod.snd = stdGaussian V ∧
      (ρ : Measure (V × V)).map (fun z => z.1 + z.2) =
        (stdGaussian _).map (fun x => f x - ∫ z, f z ∂stdGaussian _) := by
  let r := Real.sqrt (1-2*h+h^2*(L:ℝ)^2)
  have hnn : 0 ≤ 1-2*h+h^2*(L:ℝ)^2 := by nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg (L:ℝ))]
  have hr : r^2 = 1-2*h+h^2*(L:ℝ)^2 := Real.sq_sqrt hnn
  apply centered_chain_sum (r := r) (Real.sqrt_nonneg _)
  · intro x y
    have he := gradient_step_sq hL hmon hh x y
    rw [← hr, ← mul_pow] at he
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp he
  · rw [hr, Real.sq_sqrt (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hgrad hh]

#print axioms langevin_sum
#print axioms gradient_step_sq
#print axioms chain_lipschitz
#print axioms centered_chain_sum
end Green54GaussianIterations
