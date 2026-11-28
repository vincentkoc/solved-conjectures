import Mathlib

/-! The reciprocal sum on smooth numbers bounds all cofactors in a largest-prime block. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

noncomputable def smoothEuler (p : ℕ) : ℝ := ∏ q ∈ p.primesLE, (1-1/(q:ℝ))⁻¹

theorem smooth_harmonic_sum (p : ℕ) :
    HasSum (fun n : (p+1).smoothNumbers => ((n:ℕ):ℝ)⁻¹) (smoothEuler p) := by
  let f : ℕ → ℝ := fun n => (n:ℝ)⁻¹
  have geom {q : ℕ} (hq : q.Prime) : (0:ℝ)≤(q:ℝ)⁻¹ ∧ (q:ℝ)⁻¹<1 :=
    ⟨by positivity,inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)⟩
  have hpowers {q : ℕ} (hq : q.Prime) : Summable (fun n : ℕ => ‖f (q^n)‖) := by
    simpa [f,Real.norm_eq_abs,abs_of_nonneg,inv_pow] using
      summable_geometric_of_lt_one (geom hq).1 (geom hq).2
  have H := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f:=f) (by simp [f]) (fun _ => by simp [f,mul_comm]) hpowers (p+1)).2
  have value : (∏ q ∈ (p+1).primesBelow, ∑' n : ℕ, f (q^n)) = smoothEuler p := by
    apply prod_congr rfl
    intro q hq
    have h := Nat.prime_of_mem_primesLE hq
    simpa [f,one_div,inv_pow] using tsum_geometric_of_lt_one (geom h).1 (geom h).2
  rw [←value]
  exact H

theorem smooth_harmonic_bound (p : ℕ) (S : Finset ℕ)
    (hs : ∀ n∈S, n ∈ (p+1).smoothNumbers) : ∑ n ∈ S, (n:ℝ)⁻¹ ≤ smoothEuler p := by
  let f : ℕ → ℝ := fun n => (n:ℝ)⁻¹
  have H : HasSum ((p+1).smoothNumbers.indicator f) (smoothEuler p) :=
    hasSum_subtype_iff_indicator.mp (smooth_harmonic_sum p)
  have sumEq : (∑ n ∈ S, (n:ℝ)⁻¹) = ∑ n ∈ S, (p+1).smoothNumbers.indicator f n :=
    sum_congr rfl fun n hn => (Set.indicator_of_mem (hs n hn) f).symm
  rw [sumEq]
  apply sum_le_hasSum S _ H
  intro n _
  exact Set.indicator_nonneg (fun n _ => by dsimp [f]; positivity) n

#print axioms smooth_harmonic_sum
#print axioms smooth_harmonic_bound

end Arxiv.«2211.10788».IndexDivisors
