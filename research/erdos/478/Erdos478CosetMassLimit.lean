import Erdos478WilsonCosetBounds
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Vanishing occupation of a moving target with sublinear quotient set -/

namespace Erdos478.QuotientSpacing
open Finset Filter Topology
open scoped Classical
noncomputable section

private theorem small_mass {M D H : ℕ} (bound : 8*(M-1)^3≤9*D*H^2) {ε : ℝ} (pos : 0<ε)
    (small : ((D:ℝ)+1)/(H+1)<ε/2) (cube : ((D:ℝ)+1)/(H+1)<(ε/2)^3/2) :
    (M:ℝ)/(H+1)<ε := by
  let R := M-1
  have w : 0<(H:ℝ)+1 := by positivity
  have br : 8*(R:ℝ)^3≤9*D*(H:ℝ)^2 := by exact_mod_cast bound
  have norm : ((R:ℝ)/(H+1))^3≤2*(((D:ℝ)+1)/(H+1)) := by
    rw [div_pow]
    field_simp
    nlinarith [Nat.cast_nonneg (α:=ℝ) D,Nat.cast_nonneg (α:=ℝ) H,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) D) (sq_nonneg (H:ℝ)),
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) D) (Nat.cast_nonneg (α:=ℝ) H)]
  have rsmall : (R:ℝ)/(H+1)<ε/2 := by
    by_contra! bad
    have opp := pow_le_pow_left₀ (by linarith : 0≤ε/2) bad 3
    linarith
  have one : (1:ℝ)/(H+1)<ε/2 := lt_of_le_of_lt
    (div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α:=ℝ) D] : 1≤(D:ℝ)+1) w.le) small
  have m : (M:ℝ)≤R+1 := by exact_mod_cast (show M≤R+1 by dsimp [R]; omega)
  have upper := div_le_div_of_nonneg_right m w.le
  rw [add_div] at upper
  linarith

/-- All intervals and all target sets may vary along the filter. Their
quotient-set size being o(N) suffices, where N is the interval length. -/
theorem sparse_quotient_mass {ι : Type*} {l : Filter ι} (p a H : ι → ℕ)
    (S : (i : ι) → Finset (ZMod (p i)))
    (fits : ∀ᶠ i in l, (p i).Prime ∧ 1≤a i ∧ a i+H i<p i)
    (small : Tendsto (fun i => (((quotientSet (S i)).card:ℝ)+1)/(H i+1)) l (𝓝 0)) :
    Tendsto (fun i => ((hits (p i) (a i) (a i+H i) (S i)).card:ℝ)/(H i+1)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  filter_upwards [fits,small.eventually_lt_const (half_pos pos),
    small.eventually_lt_const (show 0<(ε/2)^3/2 by positivity)] with i valid low cubic
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  apply small_mass _ pos low cubic
  simpa only [Nat.add_sub_cancel_left] using target_bound valid.1 valid.2.1 valid.2.2 (S i)

/-- Even when its order exceeds the square root of the interval length,
a coset of a subgroup of order o(N) has vanishing factorial occupation. -/
theorem sparse_coset_mass {ι : Type*} {l : Filter ι} (p a H : ι → ℕ) [prime : ∀ i, Fact (p i).Prime]
    (G : (i : ι) → Subgroup (ZMod (p i))ˣ) (g : (i : ι) → (ZMod (p i))ˣ)
    (fits : ∀ᶠ i in l, 1≤a i ∧ a i+H i<p i)
    (small : Tendsto (fun i => ((Nat.card (G i):ℝ)+1)/(H i+1)) l (𝓝 0)) :
    Tendsto (fun i => ((hits (p i) (a i) (a i+H i) (unitCoset (p i) (G i) (g i))).card:ℝ)/(H i+1)) l (𝓝 0) := by
  apply sparse_quotient_mass
  · filter_upwards [fits] with i hi
    exact ⟨(prime i).out,hi⟩
  · have eq (i) : (quotientSet (unitCoset (p i) (G i) (g i))).card=Nat.card (G i) := by
      have inj : Function.Injective (fun x : G i => (x.val:ZMod (p i))) := Units.val_injective.comp Subtype.val_injective
      rw [coset_quotient_set,card_image_of_injective _ inj,card_univ,Nat.card_eq_fintype_card]
    simpa only [eq] using small

#print axioms sparse_quotient_mass
#print axioms sparse_coset_mass
end
end Erdos478.QuotientSpacing
