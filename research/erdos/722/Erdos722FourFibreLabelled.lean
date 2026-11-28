import Erdos722FourFibreCube
import Erdos722FourFibreIsolation
import Erdos722FourFibreRecovery

/-! # Labelled Steiner quadruple systems from the four-point matching family -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Finset Equiv
noncomputable section

/-- Choose an orientation of each unordered nonstar edge on the binary cube. -/
local instance cubeOrder (d : ℕ) : LinearOrder (Cube d) :=
  LinearOrder.lift' (Fintype.equivFin (Cube d)) (Fintype.equivFin _).injective

local instance cubeDec (d : ℕ) : DecidableEq (Cube d) := (cubeOrder d).toDecidableEq

abbrev CubeEdge (d : ℕ) := ↥(edges (0 : Cube d))
abbrev EdgeWord (d : ℕ) := CubeEdge d → Colour

def numberEdges (d : ℕ) := (2^d-1).choose 2

theorem cubeEdge_card (d : ℕ) : Fintype.card (CubeEdge d)=numberEdges d := by
  rw [Fintype.card_coe,edges_card]
  simp [Cube,numberEdges]

def fourLabels (d : ℕ) : Cube d × Fibre ≃ Fin (4*2^d) :=
  Fintype.equivFinOfCardEq (by simp [Cube,Fibre,mul_comm])

def labelledBlocks (d : ℕ) (R : Rule (Cube d × Fibre)) :=
  (fourLabels d).finsetCongr.finsetCongr R.blocks

theorem labelled_design (d : ℕ) (R : Rule (Cube d × Fibre)) :
    (labelledBlocks d R).IsBlockDesign 3 4 := relabel_quadruples _ R.isBlockDesign

theorem labelled_checks (d : ℕ) (R : Rule (Cube d × Fibre)) :
    Nat.card (Checks (labelledBlocks d R))=Nat.card (Checks R.blocks) :=
  Nat.card_congr (checkRelabel _ _)

def splitFamily (d : ℕ) (w : EdgeWord d) :=
  labelledBlocks d (fourRule (cubeRule d) (edgeMatching 0 w))

theorem splitFamily_design (d : ℕ) (w : EdgeWord d) : (splitFamily d w).IsBlockDesign 3 4 :=
  labelled_design ..

theorem splitFamily_injective (d : ℕ) : Function.Injective (splitFamily d) :=
  (fourLabels d).finsetCongr.finsetCongr.injective.comp (edge_blocks_injective (cubeRule d) 0)

theorem splitFamily_checks (d : ℕ) (w : EdgeWord d) :
    Nat.card (Checks (splitFamily d w))=2^(d+1)*((survivors w).card+1) := by
  rw [splitFamily,labelled_checks,edges_check_count,cube_checks_card]

private theorem rank_of_count {N k : ℕ} {D : Finset (Finset (Fin N))}
    (count : Nat.card (Checks D)=2^k) : (binaryIncidence D).rank+k=N := by
  rw [checks_card_rank,Fintype.card_fin] at count
  have := Nat.pow_right_injective (by decide : 2≤2) count
  have bound := (binaryIncidence D).rank_le_card_width
  rw [Fintype.card_fin] at bound
  omega

/-- In the split family the fixed directions determine the actual binary incidence rank. -/
theorem splitFamily_rank (d : ℕ) (w : EdgeWord d) :
    (binaryIncidence (splitFamily d w)).rank+(d+1)+
      (if w=(fun _ => 1) then 2 else if ∃ a, a∈survivors w then 1 else 0)=4*2^d := by
  classical
  rw [add_assoc]
  apply rank_of_count
  rw [splitFamily_checks,survivors_card]
  split_ifs <;> simp [pow_add]

/-- The same top rank holds for every transversal filling satisfying the
projection and pair identities on any word with no common fixed direction. -/
theorem arbitrary_filling_rank (d : ℕ) {w : EdgeWord d} (hw : w∈noDirectionWords (CubeEdge d))
    (R : Rule (Cube d × Fibre)) (h : Compatible (cubeRule d) (edgeMatching 0 w) R) :
    (labelledBlocks d R).IsBlockDesign 3 4 ∧ (binaryIncidence (labelledBlocks d R)).rank+(d+1)=4*2^d :=
  ⟨labelled_design .., rank_of_count (by
    rw [labelled_checks,all_fillings_check_count _ _ hw R h,cube_checks_card])⟩

def threeCycle : Colour := Equiv.swap 0 1 * Equiv.swap 1 2

theorem cycle_free : ∀ d, threeCycle d≠d := by decide +kernel

theorem cycle_family (d : ℕ) (hd : 2≤d) :
    (splitFamily d (fun _ => threeCycle)).IsBlockDesign 3 4 ∧
    (binaryIncidence (splitFamily d (fun _ => threeCycle))).rank+(d+1)=4*2^d := by
  have hn : 4≤2^d := calc
    4=2^2 := by decide
    _≤2^d := Nat.pow_le_pow_right (by decide) hd
  have pos : 0<Fintype.card (CubeEdge d) := by
    rw [cubeEdge_card,numberEdges]; apply Nat.choose_pos; omega
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp pos
  apply arbitrary_filling_rank d (R:=fourRule (cubeRule d) (edgeMatching 0 (fun _ => threeCycle)))
    (h:=fourRule_compatible ..)
  apply (mem_noDirectionWords _).mpr
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  exact fun a ha => cycle_free a ((mem_survivors ..).mp ha e)

end

#print axioms CubeEdge
#print axioms EdgeWord
#print axioms numberEdges
#print axioms cubeEdge_card
#print axioms fourLabels
#print axioms labelledBlocks
#print axioms labelled_design
#print axioms labelled_checks
#print axioms splitFamily
#print axioms splitFamily_design
#print axioms splitFamily_injective
#print axioms splitFamily_checks
#print axioms splitFamily_rank
#print axioms arbitrary_filling_rank
#print axioms threeCycle
#print axioms cycle_free
#print axioms cycle_family
end Erdos722.FourPoint
