import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS

/-! A diagonal congruence for the canonical theta sum. -/

namespace Arxiv.«2501.03234».ThetaDiagonal

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The multiplicative group of residue classes. -/
abbrev U (p : ℕ) := (ZMod p)ˣ

/-- Least nonnegative representative. -/
def rep (a : U p) : ℕ := (a : ZMod p).val

/-- Units with odd least representative. -/
def oddReps (p : ℕ) [Fact p.Prime] : Finset (U p) :=
  univ.filter fun a => rep a % 2 = 1

/-- The parity sign is positive on odd least representatives. -/
def sign (a : U p) : ℤ := if rep a % 2 = 1 then 1 else -1

private lemma rep_neg (a : U p) : rep (-a) = p - rep a := by
  let : NeZero (a : ZMod p) := ⟨a.ne_zero⟩
  exact ZMod.val_neg_of_ne_zero (a : ZMod p)

private lemma rep_lt (a : U p) : rep a < p := ZMod.val_lt _

private lemma neg_odd (hp : p % 2 = 1) (a : U p) :
    rep (-a) % 2 = 1 ↔ ¬ rep a % 2 = 1 := by
  rw [rep_neg]
  have := rep_lt a
  omega

private lemma sign_neg (hp : p % 2 = 1) (a : U p) : sign (-a) = -sign a := by
  simp only [sign, neg_odd hp]
  split_ifs <;> simp_all

/-- Negation pairs each odd representative with its complementary even representative. -/
private lemma sum_by_sign (hp : p % 2 = 1) (f : U p → ℤ) :
    ∑ a, f a = ∑ a ∈ oddReps p, (f a + f (-a)) := by
  classical
  rw [sum_add_distrib, oddReps, ← sum_filter_add_sum_filter_not univ
    (fun a : U p => rep a % 2 = 1) f]
  congr 1
  apply sum_nbij' (fun a => -a) (fun a => -a) <;> simp [neg_odd hp]
  intro a ha
  have he := neg_odd hp a
  omega

private lemma sum_units (f : ℕ → ℤ) :
    ∑ n ∈ Ico 1 p, f n = ∑ a : U p, f (rep a) := by
  classical
  symm
  apply sum_bij (fun a _ => rep a)
  · intro a _
    have h : rep a ≠ 0 := fun h => a.ne_zero ((ZMod.val_eq_zero _).mp h)
    exact mem_Ico.mpr ⟨by omega, rep_lt a⟩
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective p h)
  · intro n hn
    obtain ⟨hn₀, hn₁⟩ := mem_Ico.mp hn
    have hnz : (n : ZMod p) ≠ 0 := by
      intro h
      have := (ZMod.natCast_eq_zero_iff _ _).mp h
      exact hn₁.not_ge (Nat.le_of_dvd hn₀ this)
    exact ⟨Units.mk0 _ hnz, mem_univ _, ZMod.val_natCast_of_lt hn₁⟩
  · intros
    rfl

omit [Fact p.Prime] in
private lemma summand (hp : p % 2 = 1) (h j : U p) :
    (-1 : ℤ) ^ (rep j + 1 + rep h * rep j / p) =
      if rep j % 2 = 1 then sign h * sign (h * j) else sign (h * j) := by
  have hr : rep (h * j) = rep h * rep j % p := ZMod.val_mul _ _
  have he := congrArg (· % 2) (Nat.mod_add_div (rep h * rep j) p)
  change (rep h * rep j % p + p * (rep h * rep j / p)) % 2 = (rep h * rep j) % 2 at he
  rw [← hr, Nat.add_mod, Nat.mul_mod p, hp, one_mul, Nat.mul_mod (rep h) (rep j)] at he
  simp only [neg_one_pow_eq_ite, Nat.even_iff, sign]
  rcases Nat.mod_two_eq_zero_or_one (rep h) with hh | hh <;>
    rcases Nat.mod_two_eq_zero_or_one (rep j) with hj | hj <;>
    rcases Nat.mod_two_eq_zero_or_one (rep (h * j)) with hr' | hr' <;>
    simp [hh, hj, hr'] at he ⊢ <;> omega

/-- After both reflections, the summand on odd representatives depends only on the product. -/
theorem S_eq_odd_square (hp : p % 2 = 1) :
    S p = 2 * ∑ j ∈ oddReps p, ∑ h ∈ oddReps p, sign (h * j) := by
  classical
  simp only [S, S', ← Nat.cast_mul, Nat.floor_div_eq_div]
  rw [sum_comm, sum_units]
  simp_rw [sum_units, summand hp]
  have col (j : U p) : (∑ h : U p,
      if rep j % 2 = 1 then sign h * sign (h * j) else sign (h * j)) =
      if rep j % 2 = 1 then 2 * ∑ h ∈ oddReps p, sign (h * j) else 0 := by
    rw [sum_by_sign hp]
    split_ifs with hj
    · rw [mul_sum]
      apply sum_congr rfl
      intro h hh
      have ho := (mem_filter.mp hh).2
      have hs : sign h = 1 := if_pos ho
      simp [neg_mul, sign_neg hp, hs, two_mul]
    · apply sum_eq_zero
      intro h _
      simp [neg_mul, sign_neg hp]
  simp_rw [col]
  rw [← sum_filter, mul_sum]
  rfl

/-- Off-diagonal entries occur twice. Twice either sign is 2 modulo four. -/
private lemma matrix_mod_four {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α → ℤ)
    (hsym : ∀ a b, f a b = f b a) (hsign : ∀ a b, f a b = 1 ∨ f a b = -1) :
    (∑ a ∈ s, ∑ b ∈ s, f a b) ≡
      (s.card : ℤ) * (s.card - 1 : ℤ) + ∑ a ∈ s, f a a [ZMOD 4] := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [sum_insert ha, card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one,
      sum_add_distrib]
    have cross : (∑ b ∈ s, (f a b + f b a)) ≡ ∑ _ ∈ s, (2 : ℤ) [ZMOD 4] := by
      apply Int.ModEq.sum
      intro b _
      rw [← hsym a b]
      rcases hsign a b with h | h <;> rw [h] <;> decide
    rw [sum_add_distrib] at cross
    simp only [sum_const, nsmul_eq_mul] at cross
    have hr : ((s.card : ℤ) + 1) * (s.card + 1 - 1 : ℤ) =
        (s.card : ℤ) * (s.card - 1 : ℤ) + (s.card : ℤ) * 2 := by ring
    rw [hr]
    unfold Int.ModEq at *
    omega

/-- Multiplication by a square root of minus one pairs square residues with their negatives. -/
private lemma diagonal_zero (hp : p % 2 = 1) (hp4 : p % 4 = 1) :
    ∑ a ∈ oddReps p, sign (a * a) = 0 := by
  classical
  obtain ⟨i, hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hin : i ≠ 0 := by
    rintro rfl
    simp at hi
  let u : U p := Units.mk0 i hin
  have hu : u * u = -1 := Units.ext (by simpa [u] using hi.symm)
  have he := Equiv.sum_comp (Equiv.mulLeft u) (fun a : U p => sign (a * a))
  change (∑ a : U p, sign (u * a * (u * a))) = _ at he
  simp_rw [show ∀ a : U p, u * a * (u * a) = -(a * a) by
    intro a
    rw [mul_mul_mul_comm, hu, neg_one_mul], sign_neg hp] at he
  rw [sum_neg_distrib] at he
  have hzero : (∑ a : U p, sign (a * a)) = 0 := by omega
  rw [sum_by_sign hp] at hzero
  simpa [neg_mul_neg, ← two_mul, ← mul_sum] using hzero

/-- The odd representatives form one half of the nonzero residue classes. -/
theorem card_oddReps (hp : p % 2 = 1) : (oddReps p).card = p / 2 := by
  have hc := sum_by_sign (p := p) hp (fun _ => 1)
  simp only [sum_const, card_univ, ZMod.card_units, nsmul_eq_mul, mul_one] at hc
  omega

/-- The square-residue diagonal determines the full sum modulo eight at every odd prime. -/
theorem S_mod_eight_diagonal (hp : p % 2 = 1) :
    S p ≡ 2 * (((p / 2 : ℕ) : ℤ) * ((p / 2 : ℕ) - 1 : ℤ) +
      ∑ a ∈ oddReps p, sign (a * a)) [ZMOD 8] := by
  have hm := matrix_mod_four (oddReps p) (fun a b => sign (b * a))
    (fun a b => by rw [mul_comm]) (fun a b => by simp [sign]; omega)
  rw [card_oddReps hp] at hm
  rw [S_eq_odd_square hp]
  unfold Int.ModEq at *
  omega

/-- For primes equal to one modulo four, the canonical theta sum is p - 1 modulo eight. -/
theorem S_mod_eight_of_one_mod_four (p : ℕ) (hprime : p.Prime) (hp4 : p % 4 = 1) :
    S p ≡ (p : ℤ) - 1 [ZMOD 8] := by
  let : Fact p.Prime := ⟨hprime⟩
  have hp : p % 2 = 1 := by omega
  have hm := S_mod_eight_diagonal hp
  rw [diagonal_zero hp hp4, add_zero] at hm
  have hhalf : ((p / 2 : ℕ) : ℤ) = 2 * (p / 4 : ℕ) := by omega
  rw [hhalf] at hm
  have ht : (2 * ((p / 4 : ℕ) : ℤ)) * (2 * ((p / 4 : ℕ) : ℤ) - 1) =
      4 * ((p / 4 : ℕ) : ℤ)^2 - 2 * (p / 4 : ℕ) := by ring
  rw [ht, mul_sub] at hm
  unfold Int.ModEq at *
  omega

/-- The residue class five modulo eight gives a further nonvanishing class. -/
theorem S_ne_zero_of_five_mod_eight {p : ℕ} (hprime : p.Prime) (hp8 : p % 8 = 5) :
    S p ≠ 0 := by
  have hm := S_mod_eight_of_one_mod_four p hprime (by omega)
  unfold Int.ModEq at hm
  omega

end Arxiv.«2501.03234».ThetaDiagonal

#print axioms Arxiv.«2501.03234».ThetaDiagonal.S_eq_odd_square
#print axioms Arxiv.«2501.03234».ThetaDiagonal.card_oddReps
#print axioms Arxiv.«2501.03234».ThetaDiagonal.S_mod_eight_diagonal
#print axioms Arxiv.«2501.03234».ThetaDiagonal.S_mod_eight_of_one_mod_four
#print axioms Arxiv.«2501.03234».ThetaDiagonal.S_ne_zero_of_five_mod_eight
