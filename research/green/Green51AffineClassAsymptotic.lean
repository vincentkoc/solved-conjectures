import Green51DefectClassGrowth
import Mathlib.Analysis.SpecialFunctions.Choose

/-! # Quartic growth in the stable four-point-fibre range -/

namespace Green51FrameIsomorphisms
open Finset Filter Asymptotics Green53ParityThreshold Green51MissingMasks Green51Hyperplane
open scoped Classical Topology

/-- Number of affine classes for a specified number of unused sites of the circuit carrier. -/
noncomputable def defectClasses (s h : ℕ) : ℕ :=
  Nat.card (Quotient (affineSetoid (countedDoubles (2*(s+1)+2) (4*(2*s+3)-h) (threshold (2*s)))))

theorem stable_class_number {s h : ℕ} (hs : 5 ≤ s) (enough : h≤2*s+3) :
    defectClasses s h=Nat.card {t : Parts // weight t≤h} := by
  exact (table_eq_classes hs (k := 4*(2*s+3)-h) (by omega)).trans (stable_count enough)

private theorem shifted_choose_limit (c : ℕ) :
    Tendsto (fun h : ℕ => (((h+c).choose 4 : ℕ) : ℝ)/(144*(h:ℝ)^4)) atTop (𝓝 (1/3456)) := by
  have nz : ∀ᶠ n : ℕ in atTop, (fun n : ℕ => (n:ℝ)^4/(4 : ℕ).factorial) n≠0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp
    positivity
  have main := ((isEquivalent_iff_tendsto_one nz).mp (isEquivalent_choose 4)).comp (tendsto_add_atTop_nat c)
  have shift : Tendsto (fun h : ℕ => ((h:ℝ)+c)/h) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (c:ℝ)).inv₀ one_ne_zero
  have lim := (main.mul (shift.pow 4)).div_const (3456:ℝ)
  norm_num at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop 0] with h hh
  have h0 : (h:ℝ)≠0 := by positivity
  have hc : (h:ℝ)+c≠0 := by positivity
  field_simp
  ring

/-- Uniform in the choice of eligible dimension, the class count divided by the fourth power
of the defect converges to one over 3456. -/
theorem quartic_limit (s : ℕ → ℕ)
    (eligible : ∀ᶠ h in atTop, 5 ≤ s h ∧ h≤2*s h+3) :
    Tendsto (fun h : ℕ => (defectClasses (s h) h : ℝ)/(h:ℝ)^4) atTop (𝓝 (1/3456)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (shifted_choose_limit 4) (shifted_choose_limit 15)
  · filter_upwards [eligible,eventually_gt_atTop 0] with h elig hpos
    obtain ⟨a,_⟩ := defect_bounds elig.2
    rw [stable_count elig.2,←stable_class_number elig.1 elig.2] at a
    have bound : (((h+4).choose 4 : ℕ) : ℝ) ≤ 144*(defectClasses (s h) h : ℝ) := by exact_mod_cast a
    have hp : (0:ℝ)<(h:ℝ)^4 := by positivity
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hp) hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right bound hp.le]
  · filter_upwards [eligible,eventually_gt_atTop 0] with h elig hpos
    obtain ⟨_,a⟩ := defect_bounds elig.2
    rw [stable_count elig.2,←stable_class_number elig.1 elig.2] at a
    have bound : 144*(defectClasses (s h) h : ℝ) ≤ (((h+15).choose 4 : ℕ) : ℝ) := by exact_mod_cast a
    have hp : (0:ℝ)<(h:ℝ)^4 := by positivity
    apply (div_le_div_iff₀ hp (mul_pos (by norm_num) hp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right bound hp.le]

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.stable_class_number
#print axioms Green51FrameIsomorphisms.quartic_limit
