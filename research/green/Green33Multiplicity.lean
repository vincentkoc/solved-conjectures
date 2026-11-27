import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Representation multiplicity in Green's problem 33

The finite bound compares the second moments of the ordered sum and difference counts.
-/

open Finset
open scoped Pointwise

namespace Green33Multiplicity

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Number of ordered representations of `s` as the sum of two elements of `A`. -/
def reps (A : Finset G) (s : G) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 + p.2 = s).card

private def diffs (A : Finset G) (s : G) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 - p.2 = s).card

private def doubles (A : Finset G) (s : G) : ℕ :=
  (A.filter fun a => a + a = s).card

omit [AddCommGroup G] in
private lemma total_fibers {α : Type*} (A : Finset α) (f : α → G) :
    (∑ s, (A.filter fun a => f a = s).card) = A.card := by
  simpa using sum_card_fiberwise_eq_card_filter A univ f

omit [AddCommGroup G] in
private lemma sum_sq_fibers {α : Type*} [DecidableEq α] (A : Finset α) (f : α → G) :
    (∑ s, (A.filter fun a => f a = s).card ^ 2) =
      ((A ×ˢ A).filter fun p => f p.1 = f p.2).card := by
  rw [← total_fibers _ (fun p : α × α => f p.1)]
  apply sum_congr rfl
  intro s _
  rw [sq, ← card_product]
  congr 1
  ext p
  simp only [mem_product, mem_filter]
  grind

/-- Interchange the second entries of two pairs: equal sums become equal differences. -/
private lemma energy_identity (A : Finset G) :
    (∑ s, reps A s ^ 2) = ∑ s, diffs A s ^ 2 := by
  unfold reps diffs
  rw [sum_sq_fibers, sum_sq_fibers]
  let swap : ((G × G) × G × G) ≃ ((G × G) × G × G) :=
    ⟨fun ((a, b), (c, d)) => ((a, d), (c, b)), fun ((a, b), (c, d)) => ((a, d), (c, b)),
      fun _ => rfl, fun _ => rfl⟩
  apply card_equiv swap
  rintro ⟨⟨a, b⟩, c, d⟩
  simp only [mem_filter, mem_product, swap, Equiv.coe_fn_mk, sub_eq_sub_iff_add_eq_add]
  tauto

-- Off zero, the integer inequality (d - 2)(d - 3) ≥ 0 bounds each difference fiber.
-- At zero we keep its exact size |A|.
private lemma energy_lower (A : Finset G) :
    6 * A.card ^ 2 + 6 ≤ (∑ s, reps A s ^ 2) + 5 * A.card + 6 * Fintype.card G := by
  have hzero : diffs A 0 = A.card := by
    simp only [diffs, sub_eq_zero, ← diag_eq_filter, diag_card]
  have htotal : ∑ s, diffs A s = A.card ^ 2 := by
    unfold diffs
    rw [total_fibers, card_product, sq]
  have hineq (s : G) :
      5 * diffs A s + (if s = 0 then A.card ^ 2 + 6 else 0) ≤
        (diffs A s ^ 2 + 6) + (if s = 0 then 5 * A.card else 0) := by
    by_cases hs : s = 0
    · simp [hs, hzero, Nat.add_comm]
    · simp only [if_neg hs, Nat.add_zero]
      let d := diffs A s
      change 5 * d ≤ d ^ 2 + 6
      by_cases hd : d ≤ 2
      · interval_cases d <;> decide
      · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show 3 ≤ d by omega)
        rw [hj]
        nlinarith
  have h := sum_le_sum (s := univ) (fun s _ => hineq s)
  simp only [sum_add_distrib, ← mul_sum, htotal, sum_ite_eq', mem_univ, if_true,
    sum_const, card_univ, smul_eq_mul] at h
  rw [energy_identity]
  omega

/-- A residue with only one ordered representation must be a double. -/
private lemma reps_dichotomy (A : Finset G) (hA : A + A = univ) (s : G) :
    2 ≤ reps A s ∨ (reps A s = 1 ∧ 1 ≤ doubles A s) := by
  have hs : s ∈ A + A := hA ▸ mem_univ _
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hs
  have hp : (a, b) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by simp [ha, hb, hab]
  by_cases h : 2 ≤ reps A s
  · exact Or.inl h
  · right
    have hpos : 0 < reps A s := card_pos.mpr ⟨_, hp⟩
    refine ⟨by omega, ?_⟩
    have hp' : (b, a) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = s) := by
      simp [ha, hb, add_comm b a, hab]
    have heq := card_le_one_iff.mp (show reps A s ≤ 1 by omega) hp hp'
    have : a = b := congrArg Prod.fst heq
    subst b
    exact card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hab⟩⟩

private lemma energy_upper (A : Finset G) (hA : A + A = univ) (m : ℕ)
    (hcap : ∀ s, reps A s ≤ m + 4) :
    (∑ s, reps A s ^ 2) + (2 * (m + 4)) * Fintype.card G ≤
      (m + 6) * A.card ^ 2 + (m + 3) * A.card := by
  have htotal : ∑ s, reps A s = A.card ^ 2 := by
    unfold reps
    rw [total_fibers, card_product, sq]
  have hdbl : ∑ s, doubles A s = A.card := total_fibers A _
  have hineq (s : G) : reps A s ^ 2 + 2 * (m + 4) ≤
      (m + 6) * reps A s + (m + 3) * doubles A s := by
    rcases reps_dichotomy A hA s with hr | ⟨hr, hd⟩
    · -- For 2 ≤ r ≤ m + 4, expand (r - 2)(m + 4 - r) ≥ 0.
      have hcancel := Nat.sub_add_cancel (hcap s)
      have h := Nat.mul_le_mul_right ((m + 4) - reps A s) hr
      nlinarith only [h, hcancel, Nat.zero_le ((m + 3) * doubles A s),
        congrArg (fun x => x * reps A s) hcancel]
    · rw [hr]
      have h := Nat.mul_le_mul_left (m + 3) hd
      nlinarith
  have h := sum_le_sum (s := univ) (fun s _ => hineq s)
  simpa [sum_add_distrib, ← mul_sum, htotal, hdbl, mul_comm (Fintype.card G)] using h

/-- A finite cyclic two-basis with at most `m + 4` ordered representations per
residue must exceed the pair-counting density by a fixed amount for fixed `m`. -/
theorem multiplicity_bound (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = univ)
    (m : ℕ) (hcap : ∀ s, reps A s ≤ m + 4) :
    (2 * m + 2) * (q : ℕ) + 6 ≤ m * A.card ^ 2 + (m + 8) * A.card := by
  have hl := energy_lower A
  have hu := energy_upper A hA m hcap
  rw [ZMod.card] at hl hu
  nlinarith only [hl, hu]

#print axioms multiplicity_bound

end Green33Multiplicity
