import Erdos478PrescribedResidueBounds
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # A moving set of fewer than square-root many colours captures vanishing mass -/

namespace Erdos478.ReturnConcentration
open Finset Filter Topology
open scoped Classical

private theorem small_mass {M K H : ℕ} (b : 8*(M-K+1)^3 ≤ 9*(K*H+1)^2)
    {ε : ℝ} (pos : 0<ε)
    (small₁ : ((K:ℝ)+1)^2/(H+1) < ε/2)
    (small₂ : ((K:ℝ)+1)^2/(H+1) < (ε/2)^3/2) :
    (M:ℝ)/(H+1) < ε := by
  let R := M-K
  have den : 0 < (H:ℝ)+1 := by positivity
  have hKR : M ≤ K+R := by dsimp [R]; omega
  have split : (M:ℝ) ≤ K+(R:ℝ) := by exact_mod_cast hKR
  have kb : (K:ℝ)/(H+1) < ε/2 := lt_of_le_of_lt
    (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (K:ℝ),Nat.cast_nonneg (α:=ℝ) K]) den.le) small₁
  have br : 8*R^3 ≤ 9*((K+1)*(H+1))^2 := by
    calc
      _ ≤ 8*(R+1)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ ≤ _ := b
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) _)
  have real : 8*(R:ℝ)^3 ≤ 9*(((K:ℝ)+1)*((H:ℝ)+1))^2 := by exact_mod_cast br
  have norm : ((R:ℝ)/(H+1))^3 ≤ 2*(((K:ℝ)+1)^2/(H+1)) := by
    rw [div_pow]
    field_simp [den.ne']
    nlinarith [sq_nonneg (((K:ℝ)+1)*((H:ℝ)+1))]
  have rb : (R:ℝ)/(H+1) < ε/2 := by
    by_contra! bad
    have opposite := pow_le_pow_left₀ (by linarith : 0 ≤ ε/2) bad 3
    linarith
  have summed := div_le_div_of_nonneg_right split den.le
  rw [add_div] at summed
  linarith

/-- This includes adversarial choices of both the interval and its target residues at every prime. -/
theorem sparse_targets {ι : Type*} {l : Filter ι} (p a H : ι → ℕ) (S : ι → Finset ℕ)
    (fits : ∀ᶠ i in l, (p i).Prime ∧ 1≤a i ∧ a i+H i<p i)
    (small : Tendsto (fun i => (((S i).card:ℝ)+1)^2/(H i+1)) l (𝓝 0)) :
    Tendsto (fun i => ((selected (p i) (a i) (a i+H i) (S i)).card:ℝ)/(H i+1)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [fits,small.eventually_lt_const (half_pos hε),
    small.eventually_lt_const (show 0<(ε/2)^3/2 by positivity)] with i hf h₁ h₂
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  apply small_mass _ hε h₁ h₂
  simpa only [Nat.add_sub_cancel_left] using prescribed_set_bound hf.1 hf.2.1 hf.2.2 (S i)

#print axioms sparse_targets
end Erdos478.ReturnConcentration
