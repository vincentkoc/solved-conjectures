import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic

/-!
# Binary Steiner quadruple systems for Erdős 722

Label the points by binary vectors. The blocks are the four-element sets whose labels
sum to zero. Each triple completes to a block by adjoining the sum of its labels.
-/

namespace Erdos722

open Finset

/-- The affine binary construction gives a Steiner quadruple system on `2 ^ d` points.
The nonvacuous cases start at `d = 2`. -/
theorem exists_binary_quadruple_design (d : ℕ) :
    ∃ H : Finset (Finset (Fin (2 ^ d))), H.IsBlockDesign 3 4 := by
  classical
  let label : Fin (2 ^ d) ≃ (Fin d → ZMod 2) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  have twice (v : Fin d → ZMod 2) : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  let H := (univ : Finset (Finset (Fin (2 ^ d)))).filter
    fun B ↦ B.card = 4 ∧ ∑ x ∈ B, label x = 0
  have mem_blocks (B) : B ∈ H ↔ B.card = 4 ∧ ∑ x ∈ B, label x = 0 := by
    simp [H]
  refine ⟨H, fun B hB ↦ ((mem_blocks B).mp hB).1, ?_⟩
  intro S hS
  let w := label.symm (∑ x ∈ S, label x)
  have hw : label w = ∑ x ∈ S, label x := label.apply_symm_apply _
  have fresh : w ∉ S := by
    intro hmem
    obtain ⟨u, v, huv, hpair⟩ := card_eq_two.mp
      (show (S.erase w).card = 2 by rw [card_erase_of_mem hmem, hS])
    have hcancel : label w + (label u + label v) = label w + 0 := by
      simpa [hpair, huv] using (S.add_sum_erase label hmem).trans hw.symm
    exact huv (label.injective (add_right_cancel ((add_left_cancel hcancel).trans (twice _).symm)))
  refine ⟨insert w S, ⟨(mem_blocks _).mpr ⟨?_, ?_⟩, subset_insert _ _⟩, ?_⟩
  · rw [card_insert_of_notMem fresh, hS]
  · rw [sum_insert fresh, ← hw, twice]
  · rintro B ⟨hB, hSB⟩
    obtain ⟨hcard, hzero⟩ := (mem_blocks B).mp hB
    obtain ⟨z, hz, rfl⟩ := exists_eq_insert_iff.mpr ⟨hSB, by rw [hS, hcard]⟩
    rw [sum_insert hz, ← hw] at hzero
    have hzw : z = w := label.injective (add_right_cancel (hzero.trans (twice _).symm))
    rw [hzw]

end Erdos722

#print axioms Erdos722.exists_binary_quadruple_design
