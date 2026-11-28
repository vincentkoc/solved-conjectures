import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# A bounded separating integer for permuted root tuples

Multiplying the differences of the coefficient polynomials gives a single
nonzero polynomial. Its degree bounds the number of integer parameters
at which any two permuted tuples have the same weighted sum.
-/

namespace Erdos478.EffectiveResolvent

open Finset Polynomial
open scoped Polynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Evaluate a permuted tuple as coefficients in ascending order. -/
noncomputable def tag (a : Fin n → K) (σ : Equiv.Perm (Fin n)) (x : K) : K := by
  classical
  exact (Polynomial.ofFn n (a ∘ σ)).eval x

/-- Evaluate one coefficient vector as a polynomial. -/
noncomputable def evaluation (a : Fin n → K) (x : K) : K := by
  classical
  exact (Polynomial.ofFn n a).eval x

/-- A single bounded integer separates any finite collection of distinct
coefficient vectors. The bound depends on the size of the collection. -/
theorem evaluation_separator {P : Type*} [Fintype P] (hn : 0<n) (a : P ↪ (Fin n → K)) :
    ∃ b ≤ n*(Fintype.card P)^2, Function.Injective (fun t => evaluation (a t) (b:K)) := by
  classical
  let pairs : Finset (P × P) := univ.filter fun u => u.1 ≠ u.2
  let f (u : P × P) : K[X] := Polynomial.ofFn n (a u.1) - Polynomial.ofFn n (a u.2)
  let F := ∏ u ∈ pairs, f u
  have hF : F ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro u hu he
    have he' := Polynomial.injective_ofFn n (sub_eq_zero.mp he)
    exact (mem_filter.mp hu).2 (a.injective he')
  have hd : F.natDegree ≤ n*(Fintype.card P)^2 := calc
    F.natDegree ≤ ∑ u ∈ pairs, (f u).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _u ∈ pairs, n := by
      apply sum_le_sum
      intro u _
      exact (natDegree_sub_le ..).trans (max_le (Polynomial.ofFn_natDegree_lt hn _).le
        (Polynomial.ofFn_natDegree_lt hn _).le)
    _ = pairs.card*n := by simp
    _ ≤ Fintype.card (P × P)*n := Nat.mul_le_mul_right _ (card_le_univ _)
    _ = n*(Fintype.card P)^2 := by simp [pow_two,mul_comm]
  let B := n*(Fintype.card P)^2
  let pts : Finset K := (range (B+1)).image Nat.cast
  have hc : pts.card = B+1 := by simp [pts,card_image_of_injective _ Nat.cast_injective]
  have hx : ∃ b ≤ B, F.eval (b:K) ≠ 0 := by
    by_contra! he
    have hs : pts ⊆ F.roots.toFinset := by
      rintro x hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hx
      exact Multiset.mem_toFinset.mpr ((mem_roots hF).mpr (he b (by simpa [Nat.lt_succ_iff] using hb)))
    have hle := (card_le_card hs).trans (F.roots.toFinset_card_le.trans F.card_roots')
    omega
  obtain ⟨b,hb,he⟩ := hx
  refine ⟨b,hb,?_⟩
  intro σ τ h
  by_contra hne
  have hu : (σ,τ) ∈ pairs := mem_filter.mpr ⟨mem_univ _,hne⟩
  apply he
  rw [show F = ∏ u ∈ pairs, f u from rfl,eval_prod]
  exact prod_eq_zero hu (by simpa [f,evaluation,sub_eq_zero] using h)

/-- A parameter at most `n(n!)²` separates all orderings of a tuple of
distinct roots over a characteristic-zero field. -/
theorem exists_separator (hn : 0 < n) (a : Fin n ↪ K) :
    ∃ b ≤ n*n.factorial^2, Function.Injective (fun σ => tag a σ (b:K)) := by
  classical
  let e : Equiv.Perm (Fin n) ↪ (Fin n → K) :=
    ⟨fun σ => a ∘ σ,fun _ _ h => Equiv.ext fun j => a.injective (congrFun h j)⟩
  obtain ⟨M,hM,hi⟩ := evaluation_separator hn e
  exact ⟨M,by simpa [Fintype.card_perm] using hM,hi⟩

#print axioms evaluation_separator
#print axioms exists_separator
end Erdos478.EffectiveResolvent
