import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic

/-! The integral square discriminants for a quadratic factor of a shifted
degree-six geometric sum. -/

namespace CunninghamChain.JonesSextic

/-- Discriminant in the quadratic constant coefficient b. -/
def discriminant (a : ℤ) : ℤ :=
  4*a^6 - 8*a^5 + 9*a^4 - 4*a^3 - 6*a^2 + 12*a - 3

private def approx (a : ℤ) : ℤ := 8*a^3 - 8*a^2 + 5*a + 1

private lemma consecutive (u v : ℤ) (hu : 1 ≤ u)
    (lo : (u-1)^2 < v^2) (hi : v^2 < u^2) : False := by
  have hlo := sq_lt_sq.mp lo
  have hhi := sq_lt_sq.mp hi
  rw [abs_of_nonneg (by omega : 0 ≤ u-1)] at hlo
  rw [abs_of_nonneg (by omega : 0 ≤ u)] at hhi
  omega

private lemma outside (k : ℤ) (hk : 0 ≤ k) :
    (1 ≤ approx (20+k) ∧
      (approx (20+k)-1)^2 < 16*discriminant (20+k) ∧
      16*discriminant (20+k) < (approx (20+k))^2) ∧
    (1 ≤ -approx (-20-k) ∧
      (-approx (-20-k)-1)^2 < 16*discriminant (-20-k) ∧
      16*discriminant (-20-k) < (-approx (-20-k))^2) := by
  unfold approx discriminant
  repeat' constructor
  all_goals first
    | apply le_of_sub_nonneg; ring_nf; positivity
    | apply lt_of_sub_pos; ring_nf; positivity

/-- The discriminant of the remainder equation is square only at traces ±1. -/
theorem square_traces {a z : ℤ} (h : z^2 = discriminant a) : a = -1 ∨ a = 1 := by
  have test (u : ℤ) (h₁ : 1 ≤ u) (h₂ : (u-1)^2 < 16*discriminant a)
      (h₃ : 16*discriminant a < u^2) : False := by
    have he : (4*z)^2 = 16*discriminant a := by rw [← h]; ring
    exact consecutive u (4*z) h₁ (he ▸ h₂) (he ▸ h₃)
  have small : -20 < a ∧ a < 20 := by
    constructor
    · by_contra! ha
      have ⟨hp,hl,hh⟩ := (outside (-20-a) (by omega)).2
      rw [show -20-(-20-a) = a by ring] at hp hl hh
      exact test _ hp hl hh
    · by_contra! ha
      have ⟨hp,hl,hh⟩ := (outside (a-20) (by omega)).1
      rw [show 20+(a-20) = a by ring] at hp hl hh
      exact test _ hp hl hh
  have finite : ∀ i : Fin 39, let x : ℤ := (i.val : ℤ)-19
      Int.sqrt (discriminant x) * Int.sqrt (discriminant x) = discriminant x → x = -1 ∨ x = 1 := by decide +kernel
  let i : Fin 39 := ⟨(a+19).toNat, by omega⟩
  have hi : (i.val : ℤ)-19 = a := by dsimp [i]; omega
  have hf := finite i
  dsimp only at hf
  rw [hi] at hf
  exact hf ((Int.exists_mul_self _).mp ⟨z, by simpa [pow_two] using h⟩)

/-- If the linear coefficient of the sextic remainder vanishes modulo
X²+aX+b, only these three quadratic polynomials can occur. -/
theorem remainder_pairs {a b : ℤ}
    (h : (1-3*a)*b^2 + (4*a^3-3*a^2+2*a-1)*b +
      (1-a+a^2-a^3+a^4-a^5) = 0) :
    (a = -1 ∧ b = 1) ∨ (a = 1 ∧ (b = 0 ∨ b = 1)) := by
  let z := 2*(1-3*a)*b + (4*a^3-3*a^2+2*a-1)
  have hz : z^2 = discriminant a := by
    dsimp [z,discriminant]
    linear_combination 4*(1-3*a)*h
  rcases square_traces hz with ha | ha
  · subst a
    norm_num at h
    left
    refine ⟨rfl, ?_⟩
    have hb : (2*b-2)*(2*b-3) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hb with hb | hb <;> omega
  · subst a
    right
    refine ⟨rfl, ?_⟩
    norm_num at h
    have hb : b*(b-1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hb with hb | hb <;> omega

#print axioms square_traces
#print axioms remainder_pairs

end CunninghamChain.JonesSextic
