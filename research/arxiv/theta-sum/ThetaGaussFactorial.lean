import ThetaDiagonalModEight

/-! The square-residue diagonal and the quadratic character of the half-factorial. -/

namespace Arxiv.«2501.03234».ThetaFactorial

open Finset
open ThetaDiagonal (U rep sign oddReps)

variable {p : ℕ} [Fact p.Prime]

private def evenSquares (p : ℕ) [Fact p.Prime] : Finset (U p) :=
  (oddReps p).filter fun a => rep (a * a) % 2 = 0

private def squareIndices (p : ℕ) [Fact p.Prime] : Finset ℕ :=
  (Icc 1 (p / 2)).filter fun k => legendreSym p (2 * (k : ℤ)) = 1

private lemma rep_pos (a : U p) : 0 < rep a :=
  Nat.pos_of_ne_zero (fun e => a.ne_zero ((ZMod.val_eq_zero _).mp e))

private lemma rep_neg (a : U p) : rep (-a) = p - rep a := by
  let : NeZero (a : ZMod p) := ⟨a.ne_zero⟩
  exact ZMod.val_neg_of_ne_zero _

private lemma two_ne_zero {k : ℕ} (hk : k ∈ Icc 1 (p / 2)) (hp : p % 2 = 1) :
    ((2 * k : ℕ) : ZMod p) ≠ 0 := by
  obtain ⟨hl, hu⟩ := mem_Icc.mp hk
  have hlt : 2 * k < p := by omega
  intro hz
  have hv := ZMod.val_natCast_of_lt hlt
  rw [hz, ZMod.val_zero] at hv
  omega

/-- Each even nonzero square has exactly one square root with odd representative. -/
private lemma count_even_squares (hp : p % 2 = 1) :
    (evenSquares p).card = (squareIndices p).card := by
  apply card_bij (fun (a : U p) _ => rep (a * a) / 2)
  · intro a ha
    have hpar := (mem_filter.mp ha).2
    have hlo := rep_pos (a * a)
    have hlt : rep (a * a) < p := ZMod.val_lt _
    have hk : rep (a * a) / 2 ∈ Icc 1 (p / 2) := mem_Icc.mpr ⟨by omega, by omega⟩
    apply mem_filter.mpr
    refine ⟨hk, ?_⟩
    change legendreSym p ((2 * (rep (a * a) / 2) : ℕ) : ℤ) = 1
    rw [show 2 * (rep (a * a) / 2) = rep (a * a) by omega]
    apply (legendreSym.eq_one_iff' p (by simp [rep])).mpr
    exact ⟨(a : ZMod p), by simp [rep]⟩
  · intro a ha b hb he
    obtain ⟨hao, hae⟩ := mem_filter.mp ha
    obtain ⟨hbo, hbe⟩ := mem_filter.mp hb
    have hrep : rep (a * a) = rep (b * b) := by omega
    have heq : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := by
      simpa [sq] using (ZMod.val_injective p hrep)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · exact Units.ext h
    · have hneg : a = -b := Units.ext h
      have ho := (mem_filter.mp hao).2
      have ho' := (mem_filter.mp hbo).2
      rw [hneg, rep_neg] at ho
      have hlt : rep b < p := ZMod.val_lt _
      omega
  · intro k hk
    obtain ⟨hk, hsq⟩ := mem_filter.mp hk
    have hz := two_ne_zero hk hp
    have hlt : 2 * k < p := by have := (mem_Icc.mp hk).2; omega
    have hcast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
    rw [← hcast] at hsq
    obtain ⟨x, hx⟩ := (legendreSym.eq_one_iff' p hz).mp hsq
    have hxn : x ≠ 0 := by rintro rfl; rw [zero_mul] at hx; exact hz hx
    let a : U p := Units.mk0 x hxn
    have he : rep (a * a) = 2 * k := by
      change (x * x).val = 2 * k
      rw [← hx, ZMod.val_natCast_of_lt hlt]
    have lift (b : U p) (hodd : rep b % 2 = 1) (hrep : rep (b * b) = 2 * k) :
        ∃ b, ∃ _ : b ∈ evenSquares p, rep (b * b) / 2 = k := by
      refine ⟨b, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hodd⟩, by rw [hrep]; omega⟩,
        by rw [hrep]; omega⟩
    by_cases hodd : rep a % 2 = 1
    · exact lift a hodd he
    · apply lift (-a)
      · rw [rep_neg]; have hlt' : rep a < p := ZMod.val_lt _; omega
      · simpa using he

private lemma diagonal_count (hp : p % 2 = 1) :
    ∑ a ∈ oddReps p, sign (a * a) = (p / 2 : ℕ) - 2 * ((squareIndices p).card : ℤ) := by
  have signed (a : U p) : sign (a * a) =
      1 - 2 * (if rep (a * a) % 2 = 0 then 1 else 0 : ℤ) := by
    unfold sign
    rcases Nat.mod_two_eq_zero_or_one (rep (a * a)) with h | h <;> norm_num [h]
  simp_rw [signed]
  rw [sum_sub_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul, mul_one, ThetaDiagonal.card_oddReps hp,
    sum_boole]
  rw [← evenSquares, count_even_squares hp]

private lemma sym_dichotomy (hp : p % 2 = 1) {k : ℕ} (hk : k ∈ Icc 1 (p / 2)) :
    legendreSym p (2 * (k : ℤ)) = 1 ∨ legendreSym p (2 * (k : ℤ)) = -1 := by
  apply legendreSym.eq_one_or_neg_one
  exact_mod_cast two_ne_zero hk hp

/-- The diagonal is the negative quadratic excess among the even representatives. -/
theorem diagonal_eq_neg_character_sum (hp : p % 2 = 1) :
    ∑ a ∈ oddReps p, sign (a * a) = -∑ k ∈ Icc 1 (p / 2), legendreSym p (2 * (k : ℤ)) := by
  rw [diagonal_count hp]
  have hs : (∑ k ∈ Icc 1 (p / 2), legendreSym p (2 * (k : ℤ))) =
      ∑ k ∈ Icc 1 (p / 2), (2 * (if legendreSym p (2 * (k : ℤ)) = 1 then 1 else 0 : ℤ) - 1) := by
    apply sum_congr rfl
    intro k hk
    rcases sym_dichotomy hp hk with h | h <;> norm_num [h]
  rw [hs, sum_sub_distrib, ← mul_sum]
  simp only [sum_boole, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel,
    squareIndices]
  ring

/-- For a list of signs with q negative entries, the sum is n−2q and the product is (−1) ^ q. -/
private lemma sign_sum_mod_four {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (hf : ∀ k ∈ s, f k = 1 ∨ f k = -1) :
    ((∏ k ∈ s, f k) = 1 ∨ (∏ k ∈ s, f k) = -1) ∧
      (∑ k ∈ s, f k) ≡ (s.card : ℤ) - 1 + ∏ k ∈ s, f k [ZMOD 4] := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨hprod, hsum⟩ := ih (fun k hk => hf k (mem_insert_of_mem hk))
    have hsign := hf a (mem_insert_self _ _)
    rw [prod_insert ha, sum_insert ha, card_insert_of_notMem ha]
    push_cast
    unfold Int.ModEq at *
    rcases hsign with h | h <;> rcases hprod with g | g <;> rw [g] at hsum <;>
      rw [h, g] <;> constructor <;> omega

private lemma product_symbol (m : ℕ) :
    (∏ k ∈ Icc 1 m, legendreSym p (2 * (k : ℤ))) =
      legendreSym p ((2 : ℤ) ^ m * m.factorial) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ m + 1), prod_insert (by simp), ih,
      Nat.factorial_succ, pow_succ]
    push_cast
    rw [show (2 : ℤ) ^ m * 2 * ((m + 1 : ℤ) * m.factorial) =
        (2 * (m + 1 : ℤ)) * (2 ^ m * m.factorial) by ring]
    simp only [legendreSym.mul]

/-- At each odd prime, one quadratic character value determines the residue modulo eight. -/
theorem S_mod_eight_even_product (hp : p % 2 = 1) :
    S p ≡ 2 * (((p / 2 : ℕ) : ℤ) - 1) ^ 2 -
      2 * legendreSym p ((2 : ℤ) ^ (p / 2) * (p / 2).factorial) [ZMOD 8] := by
  have hm := ThetaDiagonal.S_mod_eight_diagonal hp
  rw [diagonal_eq_neg_character_sum hp] at hm
  have hs := (sign_sum_mod_four (Icc 1 (p / 2)) (fun k => legendreSym p (2 * (k : ℤ)))
    (fun _ hk => sym_dichotomy hp hk)).2
  rw [product_symbol, Nat.card_Icc, Nat.add_sub_cancel] at hs
  have hr (x y : ℤ) : 2 * (x * (x - 1) + -y) =
      2 * (x - 1) ^ 2 + 2 * (x - 1 - y) := by ring
  rw [hr] at hm
  unfold Int.ModEq at *
  omega

/-- A single Legendre symbol gives the theta sum modulo eight at primes equal to three modulo four. -/
theorem S_mod_eight_gauss_factorial (p : ℕ) (hprime : p.Prime) (hp4 : p % 4 = 3) :
    letI : Fact p.Prime := ⟨hprime⟩
    S p ≡ -2 * legendreSym p (2 * ((p / 2).factorial : ℤ)) [ZMOD 8] := by
  let : Fact p.Prime := ⟨hprime⟩
  have hp : p % 2 = 1 := by omega
  have hm := S_mod_eight_even_product hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hgt : 2 < p := by omega
    have hv := ZMod.val_natCast_of_lt hgt
    change (2 : ZMod p).val = 2 at hv
    intro e; rw [e, ZMod.val_zero] at hv; omega
  have hχ : legendreSym p 2 = 1 ∨ legendreSym p 2 = -1 :=
    legendreSym.eq_one_or_neg_one p (by simpa using h2)
  have ho : Odd (p / 2) := Nat.odd_iff.mpr (by omega)
  have hpow : legendreSym p ((2 : ℤ) ^ (p / 2)) = legendreSym p 2 := by
    change (legendreSym.hom p) ((2 : ℤ) ^ (p / 2)) = _
    rw [map_pow]
    change (legendreSym p 2) ^ (p / 2) = _
    rcases hχ with h | h <;> rw [h]
    · simp
    · exact ho.neg_one_pow
  rw [legendreSym.mul, hpow, ← legendreSym.mul] at hm
  have hhalf : ((p / 2 : ℕ) : ℤ) = 2 * ((p / 4 : ℕ) : ℤ) + 1 := by omega
  rw [hhalf, add_sub_cancel_right] at hm
  rw [show ∀ x : ℤ, 2 * (2 * x) ^ 2 = 8 * x ^ 2 by intro x; ring] at hm
  unfold Int.ModEq at *
  omega

end Arxiv.«2501.03234».ThetaFactorial

#print axioms Arxiv.«2501.03234».ThetaFactorial.diagonal_eq_neg_character_sum
#print axioms Arxiv.«2501.03234».ThetaFactorial.S_mod_eight_even_product
#print axioms Arxiv.«2501.03234».ThetaFactorial.S_mod_eight_gauss_factorial
