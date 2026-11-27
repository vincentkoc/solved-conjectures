import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Sym.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# A uniform lower bound for the factorial value set

Wilson reflection puts every nonzero even representative and every odd
representative with odd inverse in the two-factorial product set. An
order-three projectivity controls the size of the latter set. Chen and Dai use
the same Wilson inclusion with a stronger asymptotic parity estimate in
https://math.colgate.edu/~integers/g21/g21.pdf, §2.
-/

namespace Erdos478.InverseParity

open Finset

variable {p : ℕ} [Fact p.Prime]

private def rotate (x : ZMod p) : ZMod p :=
  if x = 0 ∨ x = -1 then x else -1 - x⁻¹

private theorem regular {x : ZMod p} (h0 : x ≠ 0) (h1 : x ≠ -1) :
    -1 - x⁻¹ ≠ 0 ∧ -1 - x⁻¹ ≠ -1 := by
  constructor
  · intro h
    apply h1
    field_simp [h0] at h
    linear_combination -h
  · simpa [sub_eq_self] using inv_ne_zero h0

private theorem rotate_three (x : ZMod p) : rotate (rotate (rotate x)) = x := by
  by_cases hx : x = 0 ∨ x = -1
  · simp [rotate, hx]
  obtain ⟨ha, hb⟩ := not_or.mp hx
  obtain ⟨hya, hyb⟩ := regular ha hb
  obtain ⟨hza, hzb⟩ := regular hya hyb
  simp only [rotate, if_neg hx, if_neg (not_or.mpr ⟨hya, hyb⟩), if_neg (not_or.mpr ⟨hza, hzb⟩)]
  have hu : x + 1 ≠ 0 := fun h ↦ hb (eq_neg_of_add_eq_zero_left h)
  have hform : -1 - x⁻¹ = -(x + 1) / x := by field_simp [ha]; ring
  have htwo : -1 + x / (x + 1) = -(x + 1)⁻¹ := by field_simp [hu]; ring
  rw [hform, inv_div, div_neg, sub_neg_eq_add, htwo]
  simp

private def turn : Equiv.Perm (ZMod p) where
  toFun := rotate
  invFun := fun x ↦ rotate (rotate x)
  left_inv := rotate_three
  right_inv := rotate_three

private def good (x : ZMod p) : ℕ := if x.val % 2 = x⁻¹.val % 2 then 1 else 0

private def oddHit (x : ZMod p) : ℕ := if x.val % 2 = 1 ∧ x⁻¹.val % 2 = 1 then 1 else 0

private theorem rotate_parity (hp : p % 2 = 1) (x : ZMod p) :
    (rotate x).val % 2 = x⁻¹.val % 2 := by
  by_cases hx : x = 0 ∨ x = -1
  · rcases hx with rfl | rfl <;> simp [rotate]
  have hm : (-1 : ZMod p).val = p - 1 := by
    cases p with
    | zero => omega
    | succ t => exact ZMod.val_neg_one t
  have hb := x⁻¹.val_lt
  rw [rotate, if_neg hx, ZMod.val_sub (by omega : x⁻¹.val ≤ (-1 : ZMod p).val), hm]
  omega

private theorem cycle_count (hp : p % 2 = 1) (x : ZMod p) :
    1 + (if x = 0 then 2 else 0) + (if x = -1 then 2 else 0) ≤
      good x + good (rotate x) + good (rotate (rotate x)) := by
  by_cases ha : x = 0
  · subst x
    simp [good, rotate]
  by_cases hb : x = -1
  · subst x
    simp [good, rotate]
  simp only [if_neg ha, if_neg hb, add_zero, good, ← rotate_parity hp, rotate_three]
  split_ifs <;> omega

private theorem split_good (hp : p % 2 = 1) (x : ZMod p) :
    good x = (if x = 0 then 1 else 0) + oddHit x + oddHit (-x) := by
  by_cases hx : x = 0
  · subst x
    simp [good, oddHit]
  simp only [if_neg hx, zero_add, good, oddHit, inv_neg, ZMod.neg_val, if_neg (inv_ne_zero hx)]
  have h := x.val_lt
  have h' := x⁻¹.val_lt
  split_ifs <;> omega

/-- At least (p+1)/6 residues are odd and have an odd inverse. Parity refers
to the least nonnegative representatives. -/
theorem six_mul_card_odd_inverse (hp : p % 2 = 1) :
    p + 1 ≤ 6 * (univ.filter (fun x : ZMod p ↦ x.val % 2 = 1 ∧ x⁻¹.val % 2 = 1)).card := by
  have h := sum_le_sum (s := (univ : Finset (ZMod p))) (fun x _ ↦ cycle_count hp x)
  have cycle (f : ZMod p → ℕ) : ∑ x : ZMod p, f (rotate x) = ∑ x, f x :=
    Equiv.sum_comp turn f
  have flip : ∑ x : ZMod p, oddHit (-x) = ∑ x : ZMod p, oddHit x :=
    Equiv.sum_comp (Equiv.neg _) oddHit
  simp only [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one,
    sum_ite_eq', mem_univ, if_true] at h
  rw [cycle (fun x ↦ good (rotate x)), cycle good] at h
  simp_rw [split_good hp] at h
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true, flip] at h
  simp only [oddHit, ← card_filter] at h
  norm_cast at h
  omega

private theorem reflection (i : ℕ) (hi : i < p) :
    (i.factorial : ZMod p) * ((p - 1 - i).factorial : ZMod p) = (-1 : ZMod p) ^ (i + 1) := by
  induction i with
  | zero => simp [ZMod.wilsons_lemma]
  | succ i ih =>
    have hprev := ih (by omega)
    have hstep : p - 1 - i = (p - 1 - (i + 1)) + 1 := by omega
    have hsum : (p - 1 - i) + (i + 1) = p := by omega
    have hcast : ((p - 1 - i : ℕ) : ZMod p) + (i + 1) = 0 := by
      exact_mod_cast (show (((p - 1 - i) + (i + 1) : ℕ) : ZMod p) = 0 by rw [hsum, ZMod.natCast_self])
    have hfac : (((p - 1 - i).factorial : ℕ) : ZMod p) =
        (p - 1 - i : ℕ) * (((p - 1 - (i + 1)).factorial : ℕ) : ZMod p) := by
      conv_lhs => rw [hstep, Nat.factorial_succ, Nat.cast_mul, ← hstep]
    rw [hfac] at hprev
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ = -((i.factorial : ZMod p) * ((p - 1 - i : ℕ) * ((p - 1 - (i + 1)).factorial : ZMod p))) := by
        linear_combination (i.factorial : ZMod p) * ((p - 1 - (i + 1)).factorial : ZMod p) * hcast
      _ = _ := by rw [hprev]; ring

private def values (p : ℕ) : Finset (ZMod p) :=
  (Ico 1 p).image (fun i ↦ (i.factorial : ZMod p))

private theorem mem_values (i : ℕ) (hi : i < p) : (i.factorial : ZMod p) ∈ values p := by
  cases i with
  | zero => exact mem_image.mpr ⟨1, mem_Ico.mpr ⟨le_rfl, (Fact.out : p.Prime).one_lt⟩, by simp⟩
  | succ i => exact mem_image.mpr ⟨_, mem_Ico.mpr ⟨by omega, hi⟩, rfl⟩

private theorem values_card : (values p).card =
    ((Ico 1 p).image (fun i ↦ i.factorial % p)).card := by
  rw [← card_image_of_injective (values p) (ZMod.val_injective p), values, image_image]
  simp only [Function.comp_def, ZMod.val_natCast]

/-- Products of two factorial residues, with both indices in the upstream range. -/
def factorialProducts (p : ℕ) : Finset (ZMod p) :=
  (values p).sym2.image (Sym2.lift ⟨(· * ·), mul_comm⟩)

private theorem mem_products {x y : ZMod p} (hx : x ∈ values p) (hy : y ∈ values p) :
    x * y ∈ factorialProducts p :=
  mem_image.mpr ⟨_, mk_mem_sym2_iff.mpr ⟨hx, hy⟩, rfl⟩
private theorem peel {x : ZMod p} (hx : x ≠ 0) :
    (x.val.factorial : ZMod p) = x * ((x.val - 1).factorial : ZMod p) := by
  have hpos := ZMod.val_pos.mpr hx
  have h : x.val - 1 + 1 = x.val := by omega
  conv_lhs => rw [← h, Nat.factorial_succ, Nat.cast_mul, h, ZMod.natCast_zmod_val]

private theorem even_product {x : ZMod p} (hx : x ≠ 0) (he : x.val % 2 = 0) : x ∈ factorialProducts p := by
  have hl := x.val_lt
  have hp := ZMod.val_pos.mpr hx
  have h := reflection (p := p) (x.val - 1) (by omega)
  have hpow : Even (x.val - 1 + 1) := Nat.even_iff.mpr (by omega)
  rw [hpow.neg_one_pow] at h
  have mem := mem_products (mem_values x.val hl) (mem_values (p - 1 - (x.val - 1)) (by omega))
  simpa only [peel hx, mul_assoc, h, mul_one] using mem

private theorem odd_inverse_product {x : ZMod p} (ho : x.val % 2 = 1) : x⁻¹ ∈ factorialProducts p := by
  have hx : x ≠ 0 := by rintro rfl; simp at ho
  have hl := x.val_lt
  have h := reflection (p := p) x.val hl
  have hpow : Even (x.val + 1) := Nat.even_iff.mpr (by omega)
  rw [hpow.neg_one_pow] at h
  have he : ((x.val - 1).factorial : ZMod p) * ((p - 1 - x.val).factorial : ZMod p) = x⁻¹ := by
    apply mul_left_cancel₀ hx
    rw [← mul_assoc, ← peel hx, h, mul_inv_cancel₀ hx]
  exact he ▸ mem_products (mem_values _ (by omega)) (mem_values _ (by omega))

/-- Wilson reflection and the three-cycle bound give a pointwise lower
bound for the set of products of two factorial residues. -/
theorem product_bound (hp : p % 2 = 1) : 4 * p ≤ 6 * (factorialProducts p).card + 2 := by
  let E := (range (p / 2)).image (fun i : ℕ ↦ ((2 * (i + 1) : ℕ) : ZMod p))
  let O := univ.filter (fun x : ZMod p ↦ x.val % 2 = 1 ∧ x⁻¹.val % 2 = 1)
  have erange {i : ℕ} (h : i ∈ range (p / 2)) : 2 * (i + 1) < p := by
    have := mem_range.mp h
    omega
  have ec : E.card = p / 2 := by
    dsimp [E]
    rw [card_image_of_injOn, card_range]
    intro i hi j hj eq
    have e := congrArg ZMod.val eq
    simp only [ZMod.val_natCast_of_lt (erange hi), ZMod.val_natCast_of_lt (erange hj)] at e
    omega
  have espec {x : ZMod p} (h : x ∈ E) : x ≠ 0 ∧ x.val % 2 = 0 := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    have hv := ZMod.val_natCast_of_lt (erange hi)
    exact ⟨fun h ↦ by rw [h, ZMod.val_zero] at hv; omega, by rw [hv]; omega⟩
  have dis : Disjoint E O := disjoint_left.mpr fun x he ho ↦ by
    have := (espec he).2
    have := (mem_filter.mp ho).2.1
    omega
  have sub : E ∪ O ⊆ factorialProducts p := by
    intro x hx
    rcases mem_union.mp hx with hr | hr
    · exact even_product (espec hr).1 (espec hr).2
    · simpa using odd_inverse_product (mem_filter.mp hr).2.2
  have count := card_le_card sub
  rw [card_union_of_disjoint dis, ec] at count
  have ho : p + 1 ≤ 6 * O.card := six_mul_card_odd_inverse hp
  omega

/-- For every odd prime, if a is the upstream factorial-image cardinality,
then 4p ≤ 3a(a+1)+2. -/
theorem factorial_value_bound (hp : p % 2 = 1) :
    let a := ((Ico 1 p).image (fun i ↦ i.factorial % p)).card
    4 * p ≤ 3 * a * (a + 1) + 2 := by
  dsimp only
  rw [← values_card]
  have hp' := product_bound hp
  have hc : (factorialProducts p).card ≤ ((values p).card + 1).choose 2 :=
    (card_image_le.trans_eq (card_sym2 _))
  rw [Nat.choose_two_right, Nat.add_sub_cancel] at hc
  have : 2 * (factorialProducts p).card ≤ ((values p).card + 1) * (values p).card := by omega
  nlinarith

/-- In square-root form, the leading lower-bound constant is 2 / √3. -/
theorem factorial_value_sqrt_bound (hp : p % 2 = 1) :
    2 * Real.sqrt p ≤ Real.sqrt 3 *
      ((((Ico 1 p).image (fun i ↦ i.factorial % p)).card : ℝ) + 1) := by
  let a := ((Ico 1 p).image (fun i ↦ i.factorial % p)).card
  have h : 4 * (p : ℝ) ≤ 3 * (a : ℝ) * (a + 1) + 2 := by
    exact_mod_cast factorial_value_bound hp
  change 2 * Real.sqrt p ≤ Real.sqrt 3 * ((a : ℝ) + 1)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  nlinarith [show 0 ≤ (a : ℝ) by positivity]

#print axioms factorial_value_sqrt_bound
#print axioms six_mul_card_odd_inverse
#print axioms product_bound
#print axioms factorial_value_bound

end Erdos478.InverseParity
