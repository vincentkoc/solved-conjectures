import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic and cubic factorial collisions

For Erdős 478 we count the endpoints of two different lengths of factorial
collision. The endpoint sets are disjoint, and Wilson's theorem supplies
one further endpoint. The root-count method is used by Klurman and Munsch,
*Distribution of factorials modulo p*, §2 (https://doi.org/10.5802/jtnb.974).
-/

namespace Erdos478.MixedGaps

open Finset

/-- Endpoints of a two-step factorial repetition, in field coordinates. -/
def quadratic (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun x ↦ x * (x - 1) = 1

/-- Endpoints of a three-step factorial repetition, in field coordinates. -/
def cubic (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun x ↦ x * (x - 1) * (x - 2) = 1

private theorem short_gap {p : ℕ} [Fact p.Prime] {x : ZMod p} {k : ℕ}
    (hk : k < x.val) (hprod : (x.val.descFactorial k : ZMod p) = 1) (hkpos : 0 < k) :
    ∃ j ∈ Ico 1 p, j < x.val ∧ j.factorial % p = x.val.factorial % p := by
  refine ⟨x.val - k, mem_Ico.mpr ⟨by omega, by have := x.val_lt; omega⟩,
    by omega, (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_⟩
  have h := congrArg (fun n : ℕ ↦ (n : ZMod p)) (Nat.factorial_mul_descFactorial hk.le)
  simpa only [Nat.cast_mul, hprod, mul_one] using h

private theorem nonzero_five {p : ℕ} [Fact p.Prime] (hp : 5 < p) : (5 : ZMod p) ≠ 0 :=
  fun h ↦ Nat.not_dvd_of_pos_of_lt (by decide) hp ((ZMod.natCast_eq_zero_iff 5 p).mp h)

private theorem quadratic_endpoint {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    {x : ZMod p} (hx : x ∈ quadratic p) :
    x ≠ -2 ∧ ∃ j ∈ Ico 1 p, j < x.val ∧ j.factorial % p = x.val.factorial % p := by
  have h : x * (x - 1) = 1 := (mem_filter.mp hx).2
  constructor
  · rintro rfl
    exact nonzero_five hp (by linear_combination h)
  · have hlo : 2 < x.val := by
      by_contra! hsmall
      interval_cases e : x.val <;> rw [← ZMod.natCast_zmod_val x, e] at h <;>
        norm_num at h
      exact one_ne_zero (by linear_combination h : (1 : ZMod p) = 0)
    apply short_gap hlo _ (by decide)
    simpa [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ x.val), mul_comm] using h

private theorem cubic_endpoint {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    {x : ZMod p} (hx : x ∈ cubic p) :
    x ≠ -2 ∧ ∃ j ∈ Ico 1 p, j < x.val ∧ j.factorial % p = x.val.factorial % p := by
  have h : x * (x - 1) * (x - 2) = 1 := (mem_filter.mp hx).2
  constructor
  · rintro rfl
    have hsq : (5 : ZMod p) ^ 2 = 0 := by linear_combination -h
    exact nonzero_five hp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hsq)
  · have hlo : 3 < x.val := by
      by_contra! hsmall
      interval_cases e : x.val <;> rw [← ZMod.natCast_zmod_val x, e] at h <;>
        norm_num at h
      exact nonzero_five hp (by linear_combination h)
    apply short_gap hlo _ (by decide)
    simpa [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ x.val),
      Nat.cast_sub (by omega : 2 ≤ x.val), mul_comm, mul_left_comm, mul_assoc] using h

private theorem disjoint_endpoints {p : ℕ} [Fact p.Prime] (hp : 5 < p) :
    Disjoint (quadratic p) (cubic p) := by
  apply disjoint_left.mpr
  intro x hx hy
  have h := (mem_filter.mp hx).2
  have g := (mem_filter.mp hy).2
  change x * (x - 1) = 1 at h
  change x * (x - 1) * (x - 2) = 1 at g
  rw [h, one_mul] at g
  have he : x = 3 := by linear_combination g
  rw [he] at h
  exact nonzero_five hp (by linear_combination h)

private theorem wilson_endpoint {p : ℕ} [Fact p.Prime] (hp : 5 < p) :
    (p - 2).factorial % p = 1 % p := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  have h := ZMod.wilsons_lemma p
  rw [show p - 1 = (p - 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul] at h
  push_cast [Nat.cast_sub (by omega : 2 ≤ p)] at h
  simp only [ZMod.natCast_self] at h
  push_cast
  linear_combination -h

/-- The two root counts add even when several collisions have the same factorial value. -/
theorem card_add_root_counts {p : ℕ} [Fact p.Prime] (hp : 5 < p) :
    ((Ico 1 p).image (fun k ↦ k.factorial % p)).card +
      (quadratic p).card + (cubic p).card + 2 ≤ p := by
  let roots := quadratic p ∪ cubic p
  let ends := roots.image ZMod.val
  have spec {i : ℕ} (hi : i ∈ ends) :
      i < p ∧ i ≠ p - 2 ∧ ∃ j ∈ Ico 1 p, j < i ∧ j.factorial % p = i.factorial % p := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
    have H := (mem_union.mp hx).elim (quadratic_endpoint hp) (cubic_endpoint hp)
    refine ⟨x.val_lt, fun he ↦ H.1 ?_, H.2⟩
    rw [← ZMod.natCast_zmod_val x, he, Nat.cast_sub (by omega : 2 ≤ p)]
    simp
  let t := insert (p - 2) ends
  have earlier {i} (hi : i ∈ t) :
      i ∈ Ico 1 p ∧ ∃ j ∈ Ico 1 p, j < i ∧ j.factorial % p = i.factorial % p := by
    rcases mem_insert.mp hi with rfl | hr
    · exact ⟨mem_Ico.mpr ⟨by omega, by omega⟩, 1, mem_Ico.mpr ⟨le_rfl, by omega⟩,
        by omega, by simpa using (wilson_endpoint hp).symm⟩
    · obtain ⟨hlt, _, j, hj, hji, he⟩ := spec hr
      exact ⟨mem_Ico.mpr ⟨by have := (mem_Ico.mp hj).1; omega, hlt⟩, j, hj, hji, he⟩
  let f := fun k : ℕ ↦ k.factorial % p
  have covered : (Ico 1 p).image f ⊆ ((Ico 1 p) \ t).image f := by
    intro y hy
    have h : ∃ i, i ∈ Ico 1 p ∧ f i = y := mem_image.mp hy
    obtain ⟨hi, he⟩ := Nat.find_spec h
    refine mem_image.mpr ⟨_, mem_sdiff.mpr ⟨hi, fun ht ↦ ?_⟩, he⟩
    obtain ⟨j, hj, hlt, hval⟩ := (earlier ht).2
    exact Nat.find_min h hlt ⟨hj, hval.trans he⟩
  have ct : t.card = (quadratic p).card + (cubic p).card + 1 := by
    have hnot : p - 2 ∉ ends := fun h ↦ (spec h).2.1 rfl
    rw [card_insert_of_notMem hnot, card_image_of_injective _ (ZMod.val_injective p),
      card_union_of_disjoint (disjoint_endpoints hp)]
  have ht : t ⊆ Ico 1 p := fun _ hi ↦ (earlier hi).1
  have hle := (card_le_card covered).trans card_image_le
  rw [card_sdiff_of_subset ht, Nat.card_Ico] at hle
  have htcard := card_le_card ht
  rw [Nat.card_Ico] at htcard
  change ((Ico 1 p).image f).card + _ + _ + 2 ≤ p
  omega

/-- One root of each equation forces a deficit of at least five. The second
quadratic root is its conjugate, and the two are distinct since `p ≠ 5`. -/
theorem card_le_sub_five_of_roots {p : ℕ} [Fact p.Prime] (hp : 5 < p)
    {x z : ZMod p} (hx : x * (x - 1) = 1) (hz : z * (z - 1) * (z - 2) = 1) :
    ((Ico 1 p).image (fun k ↦ k.factorial % p)).card ≤ p - 5 := by
  have hne : x ≠ 1 - x := fun he ↦ nonzero_five hp
    (by linear_combination (2 * x - 1) * he - 4 * hx)
  have hpair : {x, 1 - x} ⊆ quadratic p := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _, hx⟩
    · exact mem_filter.mpr ⟨mem_univ _, by linear_combination hx⟩
  have hcq := card_le_card hpair
  simp [hne] at hcq
  have hcc := card_pos.mpr (show (cubic p).Nonempty from ⟨z, mem_filter.mpr ⟨mem_univ _, hz⟩⟩)
  have := card_add_root_counts hp
  omega

/-- A common parameter for the quadratic and cubic yields arbitrarily large
primes with both kinds of root. At `u = 0` the integer norm is `-1`, so a
prime dividing the norm at a multiple of `M!` exceeds `M`. -/
private theorem simultaneous_roots (N : ℕ) :
    ∃ p > max N 43, p.Prime ∧
      ∃ x z : ZMod p, x * (x - 1) = 1 ∧ z * (z - 1) * (z - 2) = 1 := by
  let M := max N 43
  let u := 10 * M.factorial
  let a := u ^ 3 + 3 * u ^ 2 + 5 * u + 1
  let b := 3 * u ^ 2 + 3 * u + 1
  have hu : 10 ≤ u := by have := Nat.factorial_pos M; dsimp [u]; omega
  have hab : 2 * b ≤ a := by
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hu
    dsimp [a, b]
    rw [hv]
    ring_nf
    omega
  -- This natural number equals a² - ab - b².
  let m := (a - 2 * b) * (a + b) + b * b
  have hb2 : 2 ≤ b := by dsimp [b]; omega
  have hm : m ≠ 1 := by dsimp [m]; nlinarith [Nat.zero_le ((a - 2 * b) * (a + b))]
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hm
  let : Fact p.Prime := ⟨hp⟩
  have hF : (a : ZMod p) ^ 2 - a * b - (b : ZMod p) ^ 2 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff m p).mpr hd
    dsimp only [m] at h
    push_cast [Nat.cast_sub hab] at h
    linear_combination h
  have hlarge : M < p := by
    by_contra! hsmall
    have hfac := (ZMod.natCast_eq_zero_iff M.factorial p).mpr
      (Nat.dvd_factorial hp.pos hsmall)
    have hu0 : (u : ZMod p) = 0 := by simp [u, hfac]
    have ha1 : (a : ZMod p) = 1 := by simp [a, hu0]
    have hb1 : (b : ZMod p) = 1 := by simp [b, hu0]
    rw [ha1, hb1] at hF
    exact one_ne_zero (by linear_combination -hF : (1 : ZMod p) = 0)
  have h43 : (43 : ZMod p) ≠ 0 := fun h ↦
    Nat.not_dvd_of_pos_of_lt (by decide) (lt_of_le_of_lt (le_max_right _ _) hlarge)
      ((ZMod.natCast_eq_zero_iff 43 p).mp h)
  have hb : (b : ZMod p) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_pow (by decide), sub_zero, sub_zero] at hF
    have ha := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hF
    dsimp only [a] at ha
    dsimp only [b] at h
    push_cast at ha h
    have he : 8 * (u : ZMod p) + 1 = 0 := by linear_combination 3 * ha - (u + 2) * h
    exact h43 (by linear_combination 64 * h - (24 * u + 21) * he)
  let x : ZMod p := a / b
  have hx : x * (x - 1) = 1 := by
    dsimp [x]
    field_simp
    linear_combination hF
  have hbx : (b : ZMod p) * x = a := by dsimp [x]; field_simp
  refine ⟨p, hlarge, hp, x, (u : ZMod p) + 2 - x, hx, ?_⟩
  dsimp only [a, b] at hbx
  push_cast at hbx
  linear_combination (3 * ((u : ZMod p) + 1) - x - 1) * hx - hbx

/-- Among the primes where 5 is a square, arbitrarily large ones satisfy the
stronger bound `|A_p| ≤ p - 5` for the factorial image in Erdős 478. -/
theorem arbitrarily_large_sub_five (N : ℕ) :
    ∃ p > N, p.Prime ∧ IsSquare (5 : ZMod p) ∧
      ((Ico 1 p).image (fun k ↦ k.factorial % p)).card ≤ p - 5 := by
  obtain ⟨p, hlarge, hp, x, z, hx, hz⟩ := simultaneous_roots N
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨p, lt_of_le_of_lt (le_max_left _ _) hlarge, hp, ⟨2 * x - 1, ?_⟩,
    card_le_sub_five_of_roots (by omega) hx hz⟩
  linear_combination -4 * hx

#print axioms card_add_root_counts
#print axioms card_le_sub_five_of_roots
#print axioms arbitrarily_large_sub_five

end Erdos478.MixedGaps
