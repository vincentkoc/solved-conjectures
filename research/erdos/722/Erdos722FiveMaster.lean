import Erdos722FiveOrders
import Erdos722FiveSeeds

/-!
# Master pairwise balanced designs for block size five

The field sizes 9 and 16 and the modular directions at orders coprime to six
supply the five ordinary columns. A sixth column may be truncated.
-/

namespace Erdos722.Five
open Erdos722.Quartet Erdos722.Quartet.Transversal

private noncomputable def modular (t : ℕ) (ht : t%6=1 ∨ t%6=5) : Directions 5 t := by
  haveI : NeZero t := ⟨by omega⟩
  have h2 : IsUnit (2 : ZMod t) := ZMod.isUnit_prime_of_not_dvd (p := 2) (by decide) (by omega)
  have h3 : IsUnit (3 : ZMod t) := ZMod.isUnit_prime_of_not_dvd (p := 3) (by decide) (by omega)
  have h4 : IsUnit (4 : ZMod t) := by convert h2.mul h2 using 1; norm_num
  refine ⟨ZMod t,ZMod.card t,![0,1,2,3,4],?_⟩
  intro i j h
  fin_cases i <;> fin_cases j <;> try exact (h rfl).elim
  all_goals norm_num <;> assumption

private theorem directions {t : ℕ} (ht : Good t) : Nonempty (Directions 5 t) := by
  rcases ht with h | h | rfl | rfl
  · exact ⟨modular t (Or.inl h)⟩
  · exact ⟨modular t (Or.inr h)⟩
  · exact ⟨Directions.primePower 5 3 2 (by decide) (by decide)⟩
  · exact ⟨Directions.primePower 5 2 4 (by decide) (by decide)⟩

private theorem truncate (t r a : ℕ) (ht : Good t) (hr : r ≤ t) (ha : a ≤ 1)
    (hT : Has Sizes (t+a)) (hR : Has Sizes (r+a)) : Has Sizes (5*t+r+a) := by
  classical
  let D := (directions ht).some
  let e := (Fin.castLEEmb hr).trans (Fintype.equivFinOfCardEq D.card).symm.toEmbedding
  let V := Point 5 D.K (Fin r)
  let C : Cover V (fun x y => column x ≠ column y) Sizes :=
    (truncated D.c D.units e).change (fun _ _ _ => Iff.rfl) (by
      rintro n (rfl | rfl) <;> simp [Sizes])
  rcases (show a=0 ∨ a=1 by omega) with rfl | rfl
  · apply (Cover.fillFibers column C _).has (by simp [Point,D.card])
    intro i
    cases i with
    | none => exact (hR.realize (V := Fin r) (by simp)).relabel lastFiber
    | some i => exact (hT.realize D.card).relabel (finiteFiber i)
  · apply (Cover.adjoin column C _).has (by simp [Point,D.card])
    intro i
    cases i with
    | none => exact (hR.realize (V := Option (Fin r)) (by simp)).relabel (Equiv.optionCongr lastFiber)
    | some i =>
      exact (hT.realize (V := Option D.K) (by simp [D.card])).relabel (Equiv.optionCongr (finiteFiber i))

theorem master (u : ℕ) (hu : 3200 ≤ u) (hr : u%5 ≤ 1) : Has Sizes u := by
  apply eventual_orders (Has Sizes) _ truncate u hu hr
  intro i hi
  by_cases h : i ≤ 1
  · exact ⟨Cover.empty (fun x y hxy _ => hxy (Fin.ext (by omega)))⟩
  · apply Has.single
    unfold Sizes
    omega

#print axioms truncate
#print axioms master

end Erdos722.Five
