import Green51ExtremalPeriods
import Green51HammingOverlap

/-! # Exact deletion distance for the Hamming witnesses in Green 51 -/

namespace Green51DeletionRadius
open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical Pointwise symmDiff

/-- The fewest deletions that can change the double of this Hamming cylinder. -/
theorem cylinder_deletion_radius {s r : ℕ} (hs : 0 < s) :
    let H := ball (s + 1) r
    IsLeast {k : ℕ | ∃ B ⊆ H, B + B ≠ H + H ∧ (H \ B).card = k}
      (2 ^ r * (2 * s).choose s / 2) := by
  classical
  let d := 2 * (s + 1)
  let H := ball (s + 1) r
  obtain ⟨T, _, st⟩ := exists_subset_card_eq (show 2 * s ≤ (univ : Finset (Fin d)).card by simp [d])
  let z := (splitSupport d r).symm (T, 0)
  have wt : (splitSupport d r z).1.card = 2 * s := by simpa [z] using st
  have nz : z ≠ 0 := by
    intro zero
    have empty : (splitSupport d r (0 : Fin (d + r) → F)).1 = ∅ := active_zero d r
    rw [zero, empty, card_empty] at wt
    omega
  have present : z ∈ H + H := (ball_sum_iff z).mpr (by change (splitSupport d r z).1.card + 2 ≤ d; rw [wt]; dsimp [d]; omega)
  constructor
  · obtain ⟨B, sub, absent, cut⟩ := attainable_cost H z nz
    refine ⟨B, sub, fun eq => absent (eq ▸ present), ?_⟩
    have outer := outer_overlap z wt
    change (mates H z).card = _ at outer
    change (H \ B).card = 2 ^ r * (2 * s).choose s / 2
    rw [←outer, ←cut]
    omega
  · rintro k ⟨B, sub, ne, size⟩
    have inc : B + B ⊆ H + H := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
      exact mem_add.mpr ⟨a, sub ha, b, sub hb, rfl⟩
    obtain ⟨x, hin, out⟩ : ∃ x ∈ H + H, x ∉ B + B := by
      by_contra! h
      exact ne (Subset.antisymm inc h)
    have weight := cylinder_overlap x hin
    have low := direction_cost (A := H) (B := B) x out
    change 2 ^ r * (2 * s).choose s ≤ (mates H x).card at weight
    change (H \ B).card = k at size
    omega

open Green51NearThreshold Green51GirthFrame

/-- An explicit sharp witness for the canonical affine dimension and the first failing deletion size. -/
theorem deletion_witness {s r : ℕ} (hs : 0 < s) :
    ∃ H : Finset (𝔽₂ (2 * (s + 1) + r)),
      2 * H.card + 2 ^ r * (2 * (s + 1)).choose (s + 1) = 2 ^ (2 * (s + 1) + r) ∧
      (H + H)ᶜ.card = (2 * s + 3) * 2 ^ r ∧
      maxCosetDim F (𝔽₂ (2 * (s + 1) + r)) ↑(H + H) = 2 * s + r ∧
      IsLeast {k : ℕ | ∃ B ⊆ H, B + B ≠ H + H ∧ (H \ B).card = k} (2 ^ r * (2 * s).choose s / 2) := by
  let H := ball (s + 1) r
  obtain ⟨sz, count, avoids⟩ := hamming_ball_data (s + 1) r
  have eq : (H.dens : ℝ) = threshold (2 * (s + 1)) := by
    have realSize : (2 : ℝ) * H.card + 2 ^ r * ((2 * (s + 1)).choose (s + 1) : ℝ) = 2 ^ (2 * (s + 1) + r) := by exact_mod_cast sz
    rw [threshold, Nat.mul_div_cancel_left _ (by decide : 0 < 2), nnratCast_dens]
    unfold halfLayer
    simp only [Fintype.card_fun, Fintype.card_fin, F, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_add] at realSize ⊢
    apply (div_eq_iff (by positivity)).mpr
    field_simp
    nlinarith only [realSize]
  have cnt : (H + H)ᶜ.card = (2 * s + 3) * 2 ^ r := by
    rw [show (H + H)ᶜ.card = _ from count]; ring
  refine ⟨H, sz, cnt, ?_, cylinder_deletion_radius hs⟩
  apply flat_dimension_at_equality hs H _ avoids cnt.ge
  rw [eq, ←sub_pos, layer_step]
  exact div_pos (halfLayer_pos _) (by positivity)

end Green51DeletionRadius
#print axioms Green51DeletionRadius.cylinder_deletion_radius
#print axioms Green51DeletionRadius.deletion_witness
