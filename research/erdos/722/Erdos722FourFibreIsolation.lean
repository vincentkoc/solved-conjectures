import Erdos722FourFibreEdges
import Erdos722FourFibreWordCounts
import Erdos722FourFibreSplit

/-! # Counting the extra binary characters in the split four-point lift -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset
variable {I : Type*} [LinearOrder I] [Fintype I]

noncomputable def invariantDirections (o : I) (w : edges o → Colour) :
    Option ↥(survivors w) ≃ Invariant (edgeMatching o w) where
  toFun
    | none => ⟨none,fun _ _ => rfl⟩
    | some d => ⟨some d.val,(invariant_iff_edges o w _).mpr fun e =>
        congrArg some ((mem_survivors ..).mp d.prop e)⟩
  invFun
    | ⟨none,_⟩ => none
    | ⟨some d,h⟩ => some ⟨d,(mem_survivors ..).mpr fun e =>
        Option.some.inj ((invariant_iff_edges o w _).mp h e)⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨_|d,h⟩ <;> rfl

theorem edges_check_count (Q : Rule I) (o : I) (w : edges o → Colour) :
    Nat.card (Checks (fourRule Q (edgeMatching o w)).blocks)=
      Nat.card (Checks Q.blocks)*((survivors w).card+1) := by
  rw [split_checks_card Q _ (edge_normalized o w),← Nat.card_congr (invariantDirections o w)]
  simp

/-- No choice of transversal completion can create a nonconstant fibre check
when the normalized edge matchings have no common fixed direction. -/
theorem all_fillings_check_count (Q : Rule I) (o : I) {w : edges o → Colour}
    (bad : w∈noDirectionWords ↥(edges o)) (R : Rule (I × Fibre))
    (h : Compatible Q (edgeMatching o w) R) : Nat.card (Checks R.blocks)=Nat.card (Checks Q.blocks) := by
  apply Nat.card_congr
  apply Equiv.symm
  apply descendedChecks h (edge_normalized o w)
  rintro ⟨d,hd⟩
  have ed := (invariant_iff_edges o w (some d)).mp (fun i j => congrArg some (hd i j))
  have mem := (mem_survivors w d).mpr fun e => Option.some.inj (ed e)
  rw [card_eq_zero.mp ((mem_noDirectionWords _).mp bad)] at mem
  exact notMem_empty _ mem

#print axioms invariantDirections
#print axioms edges_check_count
#print axioms all_fillings_check_count
end Erdos722.FourPoint
