import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Option
import Mathlib.Tactic

/-!
# Three-coordinate interpolation on the finite projective line

A quadratic numerator divided by a fixed monic root-free quadratic gives
a word on the field and its point at infinity. Every three coordinates
determine a unique word, and the code contains the constant words.
-/

namespace Erdos722.PointedProduct.Quadratic
open Polynomial Finset Function
open scoped Polynomial
noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A monic quadratic with no field roots, also in characteristic two. -/
theorem denominator (F : Type*) [Field F] [Fintype F] :
    ∃ h : F[X], h.Monic ∧ h.natDegree=2 ∧ ∀ x, h.eval x≠0 := by
  classical
  let f (x : F) := x^2-x
  have hn : ¬Injective f := fun hi => zero_ne_one (hi (by simp [f] : f 0=f 1))
  have hns := mt Finite.injective_iff_surjective.mpr hn
  obtain ⟨c,hc⟩ := not_forall.mp hns
  let h : F[X] := X^2-(X+C c)
  have hd : (X+C c : F[X]).natDegree<(X^2 : F[X]).natDegree := by simp
  refine ⟨h,(monic_X_pow 2).sub_of_left (by simp),?_,?_⟩
  · change (X^2-(X+C c) : F[X]).natDegree=2
    rw [natDegree_sub_eq_left_of_natDegree_lt hd,natDegree_X_pow]
  · intro x he
    apply hc
    refine ⟨x,?_⟩
    simp only [h,eval_sub,eval_pow,eval_X,eval_add,eval_C] at he
    dsimp [f]
    linear_combination he

def word (h : F[X]) (v : Fin 3 → F) : Option F → F
  | none => ((ofFn 3) v).coeff 2
  | some x => ((ofFn 3) v).eval x/h.eval x

theorem restriction_bijective (h : F[X]) (hn : ∀ x, h.eval x≠0)
    (T : Finset (Option F)) (ht : T.card=3) :
    Bijective (fun v : Fin 3 → F => fun x : T => word h v x.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp [ht]⟩
  intro u v he
  apply injective_ofFn 3
  apply sub_eq_zero.mp
  let P := (ofFn 3) u-(ofFn 3) v
  change P=0
  by_contra hnP
  have hd : P.natDegree<3 := (natDegree_sub_le ..).trans_lt
    (max_lt (ofFn_natDegree_lt (by decide) u) (ofFn_natDegree_lt (by decide) v))
  have roots : T.eraseNone.card≤P.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    apply (mem_roots hnP).mpr
    change ((ofFn 3) u-(ofFn 3) v).eval x=0
    rw [eval_sub,sub_eq_zero]
    exact (div_left_inj' (hn x)).mp (congrFun he ⟨some x,mem_eraseNone.mp hx⟩)
  by_cases hnone : none∈T
  · have hh := congrFun he ⟨none,hnone⟩
    have hz : P.coeff 2=0 := by
      change ((ofFn 3) u-(ofFn 3) v).coeff 2=0
      rw [coeff_sub,sub_eq_zero]
      exact hh
    have heq : P.natDegree=2 := by rw [card_eraseNone_of_mem hnone,ht] at roots; omega
    exact (leadingCoeff_ne_zero.mpr hnP) (by rw [← coeff_natDegree,heq,hz])
  · rw [card_eraseNone_of_not_mem hnone,ht] at roots
    omega

omit [Fintype F] in
theorem constant_word (h : F[X]) (hm : h.Monic) (hd : h.natDegree=2) (hn : ∀ x, h.eval x≠0)
    (c : F) : ∃ v : Fin 3 → F, ∀ x, word h v x=c := by
  let P := C c*h
  have hP : P.natDegree<3 := (natDegree_C_mul_le c h).trans_lt (by omega)
  refine ⟨(toFn 3) P,?_⟩
  intro x
  cases x with
  | none =>
    change ((ofFn 3) ((toFn 3) P)).coeff 2=c
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt hP]
    simp [P,coeff_C_mul,← hd,hm.leadingCoeff]
  | some x =>
    change ((ofFn 3) ((toFn 3) P)).eval x/h.eval x=c
    rw [ofFn_comp_toFn_eq_id_of_natDegree_lt hP]
    simp [P,hn x]

#print axioms denominator
#print axioms restriction_bijective
#print axioms constant_word
end
end Erdos722.PointedProduct.Quadratic
