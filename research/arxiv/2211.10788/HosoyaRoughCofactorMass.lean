import HosoyaRoughCofactorResidues
import research.arxiv.«1104.1579».CunninghamSingularSeriesGrowth

/-! The proportion of reduced cofactor residues is bounded below by an Euler product. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Real

lemma rough_totient_fraction (L Y : ℕ) :
    ∏ p ∈ Y.primesLE, (1-1/(p:ℝ)) ≤ ((roughProduct L Y).totient:ℝ)/(roughProduct L Y) := by
  let P := roughProduct L Y
  have pos : 0 < (P:ℝ) := by exact_mod_cast roughProduct_pos L Y
  have eq : (P.totient:ℝ)=P*∏ p ∈ P.primeFactors, (1-1/(p:ℝ)) := by
    have h := congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors P)
    push_cast at h
    simpa only [one_div] using h
  change _ ≤ (P.totient:ℝ)/P
  rw [eq,mul_div_cancel_left₀ _ pos.ne']
  apply Finset.prod_le_prod_of_subset_of_le_one
  · exact roughProduct_primeFactors L Y
  · intro p hp
    have pr := Nat.prime_of_mem_primesLE hp
    have p1 : (1:ℝ) ≤ p := by exact_mod_cast pr.one_le
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr p1)
  · intro p _ _
    have : 0 ≤ 1/(p:ℝ) := by positivity
    linarith

/-- The same Euler-product estimate applies uniformly in the progression modulus. -/
theorem rough_totient_log_lower : ∀ᶠ Y : ℕ in atTop, ∀ L : ℕ,
    1/(2*exp 4*log Y) ≤ ((roughProduct L Y).totient:ℝ)/(roughProduct L Y) := by
  filter_upwards [CunninghamChain.prime_euler_product_log_bounds,eventually_ge_atTop 2] with Y e y L
  apply le_trans _ (rough_totient_fraction L Y)
  have unit_pos {p : ℕ} (hp : p∈Y.primesLE) : 0 < 1-1/(p:ℝ) := by
    have pr := Nat.prime_of_mem_primesLE hp
    have pos : 0 < (p:ℝ) := by exact_mod_cast pr.pos
    exact sub_pos.mpr ((div_lt_one pos).mpr (by exact_mod_cast pr.one_lt))
  let F := ∏ p ∈ Y.primesLE, (1-1/(p:ℝ))
  have fp : 0 < F := prod_pos (fun p hp => unit_pos hp)
  have inv : F⁻¹ ≤ 2*exp 4*log Y := by simpa only [F,Finset.prod_inv_distrib] using e.2
  have lp : 0 < log (Y:ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  change 1/(2*exp 4*log Y) ≤ F
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_inv_cancel₀ fp.ne'] using mul_le_mul_of_nonneg_left inv fp.le

#print axioms rough_totient_log_lower

end Arxiv.«2211.10788».IndexDivisors
