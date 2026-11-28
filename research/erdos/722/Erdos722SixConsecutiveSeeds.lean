import Erdos722QuartetSeeds
import Erdos722ProjectiveUnitals

/-!
# Consecutive local sizes for six-point blocks

A cyclic difference family on 151 points and the lines of projective
three-space over the five-element field supply the two group counts
30 and 31 after a point is deleted.
-/

namespace Erdos722.Six
open Erdos722.Quartet Finset

/-- Deleting a point from this design gives groups of five. -/
def Local (u : ℕ) := Has (· = 6) (5*u+1)

private def blocks : Fin 5 → Fin 6 → ZMod 151 :=
  ![![0,1,12,33,83,90],
    ![0,8,96,113,60,116],
    ![0,19,77,23,67,49],
    ![0,59,104,135,65,25],
    ![0,64,13,149,27,22]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem local_thirty : Local 30 := by
  change Has (· = 6) 151
  exact (show Fintype.card (ZMod 151) = 151 by simp) ▸
    Seeds.development blocks (by unfold Function.Injective; decide +kernel)
      (by unfold ExistsUnique; decide +kernel)

theorem local_thirty_one : Local 31 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h5 : Nat.card (ZMod 5) = 5 := by rw [Nat.card_eq_fintype_card,ZMod.card]
  have seed : ∃ H : Finset (Finset (Fin 6)), H.IsBlockDesign 2 6 :=
    (Has.single (s := (· = 6)) rfl).some.design
  have at_six (n : ℕ) (h : n=6) : ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 6 := h ▸ seed
  have base := at_six (Nat.card (ZMod 5)+1) (by rw [h5])
  have out := HermitianUnital.projective_design (ZMod 5) 4 6 base
  have hcard : (∑ i ∈ range 4, Nat.card (ZMod 5)^i) = 156 := by
    rw [h5]
    decide
  rw [hcard] at out
  obtain ⟨H,hH⟩ := out
  exact ⟨Cover.ofDesign hH⟩

#print axioms local_thirty
#print axioms local_thirty_one

end Erdos722.Six
