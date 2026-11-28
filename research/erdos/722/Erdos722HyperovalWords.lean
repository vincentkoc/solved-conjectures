import Erdos722ProjectiveQuadraticWords
import Mathlib.Algebra.CharP.Two

/-!
# Three-coordinate interpolation on an even-field hyperoval

Extend the projective quadratic evaluations by the coefficient of X.
Over every finite field of characteristic two, any three of the q+2
coordinates determine a unique word. This gives Hanani's TD(3,6,4)
when the alphabet has four elements.
-/

namespace Erdos722.TwoStem
open Finset Function Polynomial PointedProduct
open scoped Polynomial
noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

def hyperWord (v : Fin 3 → F) : Option (Option F) → F
  | none => v 1
  | some z => Quadratic.word (1 : F[X]) v z

private theorem finite_value (v : Fin 3 → F) (x : F) :
    hyperWord v (some (some x))=v 0+v 1*x+v 2*x^2 := by
  change ((ofFn 3) v).eval x/(1:F[X]).eval x=_
  rw [eval_one,div_one,eval_eq_sum_range' (ofFn_natDegree_lt (by decide) v)]
  simp [sum_range_succ,ofFn_coeff_eq_val_of_lt]

private theorem infinity_value (v : Fin 3 → F) : hyperWord v (some none)=v 2 :=
  ofFn_coeff_eq_val_of_lt v (by decide)

/-- The enlarged projective code has index one on every three coordinates. -/
theorem hyperoval_bijective [Fintype F] [CharP F 2] (S : Finset (Option (Option F))) (hs : S.card=3) :
    Bijective (fun v : Fin 3 → F => fun x : S => hyperWord v x.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp [hs]⟩
  intro u v he
  have agree {z} (hz : z∈S) : hyperWord u z=hyperWord v z := congrFun he ⟨z,hz⟩
  by_cases hn : none∈S
  · have e1 : u 1=v 1 := agree hn
    have n2 : S.eraseNone.card=2 := by rw [card_eraseNone_of_mem hn,hs]
    have finite_eq {x : F} (hx : x∈S.eraseNone.eraseNone) :
        u 0+u 1*x+u 2*x^2=v 0+v 1*x+v 2*x^2 := by
      simpa only [finite_value] using agree (mem_eraseNone.mp (mem_eraseNone.mp hx))
    have done_ {x : F} (hx : x∈S.eraseNone.eraseNone) (e2 : u 2=v 2) : u=v := by
      have e0 : u 0=v 0 := by simpa only [e1,e2,add_left_inj] using finite_eq hx
      funext i
      fin_cases i <;> assumption
    by_cases hi : none∈S.eraseNone
    · have pos : 0<S.eraseNone.eraseNone.card := by rw [card_eraseNone_of_mem hi,n2]; decide
      obtain ⟨x,hx⟩ := card_pos.mp pos
      exact done_ hx (by simpa only [infinity_value] using agree (mem_eraseNone.mp hi))
    · obtain ⟨x,y,hxy,hS⟩ := card_eq_two.mp ((card_eraseNone_of_not_mem hi).trans n2)
      have hx : x∈S.eraseNone.eraseNone := by simp [hS]
      have hy : y∈S.eraseNone.eraseNone := by simp [hS]
      have sqne : x^2≠y^2 := by
        intro eq
        apply hxy
        simpa only [sq_eq_sq_iff_eq_or_eq_neg,CharTwo.neg_eq,or_self] using eq
      have prod : (u 2-v 2)*(x^2-y^2)=0 := by
        linear_combination finite_eq hx - finite_eq hy - (x-y)*e1
      exact done_ hx (sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right (sub_ne_zero.mpr sqne)))
  · apply (Quadratic.restriction_bijective (1:F[X]) (by simp) S.eraseNone
      ((card_eraseNone_of_not_mem hn).trans hs)).injective
    exact funext fun x => agree (mem_eraseNone.mp x.prop)

#print axioms hyperoval_bijective
end
end Erdos722.TwoStem
