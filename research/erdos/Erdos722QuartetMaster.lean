import Erdos722QuartetDirections
import Erdos722QuartetTransversals

/-!
# Pairwise balanced designs for Hanani's recursion

The five permitted block sizes are the inputs to the final inflation. The
small exceptional orders use four full groups with or without a shared point.
-/

namespace Erdos722.Quartet
open Transversal

def Allowed (n : ℕ) := n = 4 ∨ n = 5 ∨ n = 8 ∨ n = 9 ∨ n = 12

private theorem truncate {t u : ℕ} (D : Directions 4 t) (hu : u ≤ t)
    (ht : Has Allowed t) (h : Has Allowed u) : Has Allowed (4*t+u) := by
  classical
  let e := (Fin.castLEEmb hu).trans (Fintype.equivFinOfCardEq D.card).symm.toEmbedding
  let V := Point 4 D.K (Fin u)
  let C : Cover V (fun x y => column x ≠ column y) Allowed :=
    (truncated D.c D.units e).change (fun _ _ _ => Iff.rfl) (by
      rintro n (rfl | rfl) <;> simp [Allowed])
  apply (Cover.fillFibers column C _).has (by simp [Point,D.card])
  intro i
  cases i with
  | none => exact (h.realize (V := Fin u) (by simp)).relabel lastFiber
  | some i => exact (ht.realize D.card).relabel (finiteFiber i)

private theorem four_groups {t : ℕ} (D : Directions 3 t) (h : Has Allowed t) :
    Has Allowed (4*t) := by
  classical
  let V := Point 3 D.K D.K
  let C : Cover V (fun x y => column x ≠ column y) Allowed :=
    (full D.c D.units).change (fun _ _ _ => Iff.rfl) (by rintro n rfl; exact Or.inl rfl)
  apply (Cover.fillFibers column C _).has (by simp [Point,D.card]; omega)
  intro i
  cases i with
  | none => exact (h.realize D.card).relabel lastFiber
  | some i => exact (h.realize D.card).relabel (finiteFiber i)

private theorem four_groups_with_point {t : ℕ} (D : Directions 3 t) (h : Has Allowed (t+1)) :
    Has Allowed (4*t+1) := by
  classical
  let V := Point 3 D.K D.K
  let C : Cover V (fun x y => column x ≠ column y) Allowed :=
    (full D.c D.units).change (fun _ _ _ => Iff.rfl) (by rintro n rfl; exact Or.inl rfl)
  apply (Cover.adjoin column C _).has (by simp [Point,D.card]; omega)
  let A := h.realize (V := Option D.K) (by simp [D.card])
  intro i
  cases i with
  | none => exact A.relabel (Equiv.optionCongr lastFiber)
  | some i => exact A.relabel (Equiv.optionCongr (finiteFiber i))

private theorem small_master {n : ℕ} (hn : n ≤ 12) (ha : QuartetOrders.admissible n) :
    Has Allowed n := by
  unfold QuartetOrders.admissible at ha
  by_cases hs : n ≤ 1
  · exact ⟨Cover.empty (fun x y h _ => h (Fin.ext (by omega)))⟩
  · apply Has.single
    unfold Allowed
    omega

/-- The two local pair designs, of orders 13 and 28, close the finite list of exceptions. -/
theorem master (h13 : Has Allowed 13) (h28 : Has Allowed 28) (n : ℕ)
    (hn : QuartetOrders.admissible n) : Has Allowed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n ≤ 12
    · exact small_master h hn
    rcases QuartetOrders.decompose (by omega) hn with hbase | ⟨t,u,rfl,hu,htn,hun,ht,ha,hd⟩
    · simp [QuartetOrders.baseExceptions] at hbase
      rcases hbase with rfl | rfl | rfl | rfl | rfl
      · exact h13
      · exact h28
      · exact four_groups_with_point (Directions.primePower 3 7 1 (by decide) (by decide))
          (Has.single (by simp [Allowed]))
      · exact four_groups Directions.twelve (Has.single (by simp [Allowed]))
      · exact four_groups_with_point Directions.twelve h13
    · exact truncate (Directions.four hd).some hu (ih t htn ht) (ih u hun ha)

#print axioms master

end Erdos722.Quartet
