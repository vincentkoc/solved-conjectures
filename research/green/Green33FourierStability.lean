import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Finite

open Finset Filter
open scoped Pointwise Topology

namespace Green33Fourier

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private def fiber {α : Type*} (B : Finset α) (f : α → G) (s : G) : ℕ :=
  (B.filter fun b => f b = s).card

omit [AddCommGroup G] in
private lemma fiber_weight {α R : Type*} [Semiring R]
    (B : Finset α) (f : α → G) (w : G → R) :
    ∑ s, (fiber B f s : R) * w s = ∑ b ∈ B, w (f b) := by
  classical
  simp only [fiber, card_eq_sum_ones, Nat.cast_sum, sum_mul, sum_filter]
  rw [sum_comm]
  simp

/-- Twice the number of unordered representations is the ordered count plus the diagonal count. -/
private lemma two_le_fibers (A : Finset G) (hA : A + A = univ) (s : G) :
    2 ≤ fiber (A ×ˢ A) (fun p => p.1 + p.2) s + fiber A (fun a => a + a) s := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp (show s ∈ A + A from hA ▸ mem_univ _)
  have hp : (a, b) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by simp [ha, hb, hab]
  by_cases h : a = b
  · subst b
    have hr := card_pos.mpr ⟨_, hp⟩
    have hd : 0 < fiber A (fun a => a + a) s := card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hab⟩⟩
    exact Nat.add_le_add (show 1 ≤ fiber (A ×ˢ A) (fun p => p.1 + p.2) s from hr) hd
  · have hp' : (b, a) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by
      simp [ha, hb, add_comm b a, hab]
    have hr := one_lt_card.mpr ⟨_, hp, _, hp', fun he => h (congrArg Prod.fst he)⟩
    exact le_add_right hr

/-- For a nontrivial additive character, the unordered-pair excess controls the
square of the character sum together with its diagonal correction. -/
theorem character_excess_bound (A : Finset G) (hA : A + A = univ)
    (χ : AddChar G ℂ) (hχ : χ ≠ 0) :
    ‖(∑ a ∈ A, χ a) ^ 2 + ∑ a ∈ A, χ (a + a)‖ + 2 * (Fintype.card G : ℝ) ≤
      (A.card : ℝ) ^ 2 + A.card := by
  classical
  let r := fiber (A ×ˢ A) (fun p : G × G => p.1 + p.2)
  let d := fiber A (fun a => a + a)
  let e (s : G) := r s + d s - 2
  have he (s : G) : e s + 2 = r s + d s := Nat.sub_add_cancel (two_le_fibers A hA s)
  have hmass : ∑ s, e s + 2 * Fintype.card G = A.card ^ 2 + A.card := by
    have h := congrArg (fun f : G → ℕ => ∑ s, f s) (funext he)
    have hr : ∑ s, r s = A.card ^ 2 := by
      simpa [r, sq] using fiber_weight (A ×ˢ A) (fun p : G × G => p.1 + p.2) (fun _ => (1 : ℕ))
    have hd : ∑ s, d s = A.card := by
      simpa [d] using fiber_weight A (fun a => a + a) (fun _ => (1 : ℕ))
    simpa [sum_add_distrib, hr, hd, mul_comm] using h
  have hsum : ∑ s, (e s : ℂ) * χ s = (∑ a ∈ A, χ a) ^ 2 + ∑ a ∈ A, χ (a + a) := by
    have hsplit (s : G) : (e s : ℂ) * χ s + 2 * χ s =
        (r s : ℂ) * χ s + (d s : ℂ) * χ s := by
      rw [← add_mul, ← add_mul]
      congr 1
      exact_mod_cast he s
    have h := sum_congr (s₁ := univ) rfl fun s _ => hsplit s
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, AddChar.sum_eq_zero_iff_ne_zero.2 hχ,
      mul_zero, add_zero] at h
    unfold r d at h
    rw [fiber_weight, fiber_weight] at h
    simpa [sum_product, χ.map_add_eq_mul, sq, sum_mul, mul_sum, mul_comm] using h
  rw [← hsum]
  have hle := norm_sum_le (s := univ) (f := fun s => (e s : ℂ) * χ s)
  simp only [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_natCast] at hle
  have hm : (∑ s, (e s : ℝ)) + 2 * (Fintype.card G : ℝ) = (A.card : ℝ) ^ 2 + A.card := by
    exact_mod_cast hmass
  linarith

/-- A bound independent of the diagonal character sum. -/
theorem character_norm_sq_bound (A : Finset G) (hA : A + A = univ)
    (χ : AddChar G ℂ) (hχ : χ ≠ 0) :
    ‖∑ a ∈ A, χ a‖ ^ 2 + 2 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ^ 2 + 2 * A.card := by
  let S := ∑ a ∈ A, χ a
  let D := ∑ a ∈ A, χ (a + a)
  have h := character_excess_bound A hA χ hχ
  change ‖S ^ 2 + D‖ + _ ≤ _ at h
  have htri : ‖S‖ ^ 2 ≤ ‖S ^ 2 + D‖ + ‖D‖ := by
    calc
      ‖S‖ ^ 2 = ‖S ^ 2 + D - D‖ := by rw [show S ^ 2 + D - D = S ^ 2 by ring, norm_pow]
      _ ≤ _ := norm_sub_le _ _
  have hdiag : ‖D‖ ≤ (A.card : ℝ) := by
    simpa [D] using norm_sum_le A (fun a => χ (a + a))
  change ‖S‖ ^ 2 + _ ≤ _
  linarith

/-- At Green's density, every choice of a nontrivial character, allowed to
vary with the modulus, has character sum of size o(√q). -/
theorem tendsto_normalized_character_sum {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i))) (χ : (i : ι) → AddChar (ZMod (q i)) ℂ)
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop) (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2)))
    (hχ : ∀ i, χ i ≠ 0) :
    Tendsto (fun i => ‖∑ a ∈ A i, χ i a‖ / Real.sqrt (q i)) l (𝓝 0) := by
  let x (i : ι) : ℝ := (A i).card / Real.sqrt (q i)
  let y (i : ι) := ‖∑ a ∈ A i, χ i a‖ / Real.sqrt (q i)
  have hx : Tendsto x l (𝓝 (Real.sqrt 2)) := hd
  have hlin : Tendsto (fun i => x i / Real.sqrt (q i)) l (𝓝 0) :=
    hx.div_atTop (Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq))
  have hu : Tendsto (fun i => x i ^ 2 + 2 * (x i / Real.sqrt (q i)) - 2) l (𝓝 0) := by
    convert (((hx.pow 2).add ((tendsto_const_nhds (x := (2 : ℝ))).mul hlin)).sub
      (tendsto_const_nhds (x := (2 : ℝ)))) using 1
    norm_num
  have hub (i : ι) : y i ^ 2 ≤ x i ^ 2 + 2 * (x i / Real.sqrt (q i)) - 2 := by
    have h := character_norm_sq_bound (A i) (hA i) (χ i) (hχ i)
    rw [ZMod.card] at h
    have hpos : 0 < (q i : ℝ) := by exact_mod_cast (q i).pos
    dsimp only [x, y]
    field_simp [(Real.sqrt_pos.2 hpos).ne']
    rw [Real.sq_sqrt hpos.le]
    linarith
  have hz := squeeze_zero (fun i => sq_nonneg (y i)) hub hu
  have hy (i : ι) : 0 ≤ y i := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  simpa only [Real.sqrt_sq (hy _), Real.sqrt_zero] using hz.sqrt

#print axioms character_excess_bound
#print axioms character_norm_sq_bound
#print axioms tendsto_normalized_character_sum

end Green33Fourier
