import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Square classes in a quadratic field

If adjoining a square root of `d` makes `a` a square, then `a` or
`a*d` was already a square in the base field.
-/

namespace Erdos478.SquareClasses
open Polynomial IntermediateField
noncomputable section

theorem sqrt_minpoly {F L : Type*} [Field F] [Field L] [Algebra F L]
    {d : F} {s : L} (hd : ∀ x : F, x^2 ≠ d) (hs : s^2 = algebraMap F L d) :
    minpoly F s = X^2 - C d := by
  exact (minpoly.eq_of_irreducible_of_monic
    ((X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr hd)
    (by simp [hs]) (monic_X_pow_sub_C _ (by decide))).symm

theorem sqrt_adjoin_degree {F L : Type*} [Field F] [Field L] [Algebra F L]
    {d : F} {s : L} (hd : ∀ x : F, x^2 ≠ d) (hs : s^2 = algebraMap F L d) :
    Module.finrank F F⟮s⟯ = 2 := by
  have hi : IsIntegral F s := ⟨_, monic_X_pow_sub_C d (by decide : 2≠0), by simp [hs]⟩
  rw [adjoin.finrank hi, sqrt_minpoly hd hs, natDegree_X_pow_sub_C]

private theorem sqrt_not_scalar {F L : Type*} [Field F] [Field L] [Algebra F L]
    {d : F} {s : L} (hd : ∀ x : F, x^2 ≠ d) (hs : s^2 = algebraMap F L d)
    (b : F) : s ≠ algebraMap F L b := by
  rintro rfl
  exact hd b ((algebraMap F L).injective (by simpa using hs))

private theorem coordinates {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] {d : F} {s : L}
    (hd : ∀ x : F, x^2 ≠ d) (hs : s^2 = algebraMap F L d) (hL : Module.finrank F L=2)
    (y : L) : ∃ u v : F, y=algebraMap F L u + algebraMap F L v*s := by
  classical
  let e : Fin 2 → L := ![1,s]
  have ind : LinearIndependent F e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h : algebraMap F L (c 0)+algebraMap F L (c 1)*s=0 := by
      simpa [Fin.sum_univ_two,e,Algebra.smul_def] using hc
    have h1 : c 1=0 := by
      by_contra hn
      apply sqrt_not_scalar hd hs (-(c 0)/(c 1))
      rw [map_div₀,map_neg,eq_div_iff ((_root_.map_ne_zero (algebraMap F L)).mpr hn)]
      linear_combination h
    have h0 : c 0=0 := by simpa [h1] using h
    fin_cases i <;> assumption
  let b := basisOfLinearIndependentOfCardEqFinrank ind (by simpa using hL.symm)
  refine ⟨b.repr y 0,b.repr y 1, ?_⟩
  have h := b.sum_repr y
  have hb : ⇑b=e := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  rw [Fin.sum_univ_two] at h
  simpa [hb,e,Algebra.smul_def] using h.symm

/-- Descent of a square from a quadratic extension in characteristic zero. -/
theorem square_descent {F L : Type*} [Field F] [Field L] [Algebra F L] [CharZero F]
    [FiniteDimensional F L] {a d : F} {s y : L}
    (hd : ∀ x : F, x^2 ≠ d) (hs : s^2=algebraMap F L d)
    (hL : Module.finrank F L=2) (hy : y^2=algebraMap F L a) :
    (∃ x : F, x^2=a) ∨ ∃ x : F, x^2=a*d := by
  obtain ⟨u,v,rfl⟩ := coordinates hd hs hL y
  have h : algebraMap F L (2*u*v)*s = algebraMap F L (a-u^2-v^2*d) := by
    simp only [map_mul,map_pow,map_sub,map_ofNat]
    linear_combination hy - (algebraMap F L v)^2 * hs
  have hv : 2*u*v=0 := by
    by_contra hn
    apply sqrt_not_scalar hd hs ((a-u^2-v^2*d)/(2*u*v))
    rw [map_div₀,eq_div_iff ((_root_.map_ne_zero (algebraMap F L)).mpr hn),mul_comm]
    exact h
  rcases mul_eq_zero.mp hv with h'|h'
  · have hu : u=0 := (mul_eq_zero.mp h').resolve_left (by norm_num)
    right
    refine ⟨v*d, ?_⟩
    apply (algebraMap F L).injective
    simp only [map_mul,map_pow]
    simp only [hu,map_zero,zero_add,mul_pow,hs] at hy
    rw [← hy]
    ring
  · left
    exact ⟨u,(algebraMap F L).injective (by simpa [h'] using hy)⟩

#print axioms sqrt_minpoly
#print axioms sqrt_adjoin_degree
#print axioms square_descent
end
end Erdos478.SquareClasses
