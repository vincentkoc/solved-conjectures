import Erdos478EvenGapGalois
import Erdos478EvenGapDensityCost

/-!
# Explicit densities for simultaneously saturated even gaps

All chosen gaps are imposed on the same prime. The reciprocal degree bound
also allows a prescribed progression, with no independence hypothesis.
-/

namespace Erdos478.SplittingDensity
open Finset Real

def evenLengths (R : Finset ℕ) : Finset ℕ := R.image (2*·)

theorem paired_degree_bound {m : ℕ} (hm : 0<m) (R : Finset ℕ) (hR : ∀ r∈R, 0<r) :
    Module.finrank ℚ (SplitField (test m (evenLengths R))) ≤ m.totient * pairingProduct R := by
  let weight (k : ℕ) := 2^(k/2) * (k/2).factorial
  have hpos : ∀ k∈evenLengths R, 0<k := by
    rintro _ hk
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    exact Nat.mul_pos (by decide) (hR r hr)
  apply (field_degree_bound_of hm _ hpos weight (by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    simpa [weight] using even_gap_field_degree (hR r hr))).trans_eq
  congr 1
  rw [evenLengths,prod_image (by intro i _ j _ h; exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h)]
  simp [weight,pairingProduct]

/-- Each even gap contributes at most one sign choice per pair of roots
and a permutation of its pairs to the denominator of the density. -/
theorem paired_density_bound {m : ℕ} (hm : 0<m) (R : Finset ℕ) (hR : ∀ r∈R, 0<r) :
    ((m.totient * pairingProduct R : ℕ):ℝ)⁻¹ ≤ splitDensity m (evenLengths R) := by
  apply inv_anti₀ (by exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=SplitField (test m (evenLengths R)))))
  exact_mod_cast paired_degree_bound hm R hR

theorem initial_even_sum (n : ℕ) : (∑ k∈evenLengths (Icc 1 n), k) = n*(n+1) := by
  rw [evenLengths,sum_image (by intro i _ j _ h; exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h),
    ← mul_sum]
  exact double_sum_halves n

/-- The first `n` even gaps force `D=n*(n+1)` collisions on a prime set
of density at least `exp (-(D/4)*log(4D)) / φ(m)`. -/
theorem initial_even_density_bound {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    exp (-(((n*(n+1):ℕ):ℝ)/4 * log (4*((n*(n+1):ℕ):ℝ)))) / (m.totient:ℝ) ≤
      splitDensity m (evenLengths (Icc 1 n)) := by
  let R := Icc 1 n
  have hb := paired_density_bound hm R (fun r hr => (mem_Icc.mp hr).1)
  have hp : 0<(pairingProduct R : ℝ) := by
    exact_mod_cast (Finset.prod_pos (s:=R) (fun r _ =>
      Nat.mul_pos (by positivity : 0<2^r) (Nat.factorial_pos r)))
  have H := Real.exp_le_exp.mpr (log_pairing_product hn)
  change exp (log (pairingProduct R:ℝ)) ≤ _ at H
  rw [exp_log hp] at H
  rw [exp_neg,div_eq_inv_mul]
  apply le_trans (mul_le_mul_of_nonneg_left (inv_anti₀ hp H) (by positivity))
  simpa [Nat.cast_mul,mul_comm] using hb

#print axioms paired_degree_bound
#print axioms paired_density_bound
#print axioms initial_even_sum
#print axioms initial_even_density_bound
end Erdos478.SplittingDensity
