import Erdos722AffineCosetBlocks
import Erdos722RecoverBlockCoefficients

/-! # Independent normalized linear charts on the quadruples of an affine coset -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
variable {I : Type*} [DecidableEq I] [Fintype I] {Q : Rule I}

def blockOrigin (B : Q.blocks) : I :=
  (card_pos.mp (by rw [((Q.mem_blocks _).mp B.prop).1]; decide : 0<B.val.card)).choose

theorem blockOrigin_mem (B : Q.blocks) : blockOrigin B∈B.val := Classical.choose_spec _

def freeSlots (B : Q.blocks) := B.val.erase (blockOrigin B)

theorem freeSlots_card (B : Q.blocks) : (freeSlots B).card=3 := by
  rw [freeSlots,card_erase_of_mem (blockOrigin_mem B),((Q.mem_blocks _).mp B.prop).1]

abbrev CosetPattern (d : ℕ) := (B : cosetBlocks d) → freeSlots B.val → Colour

theorem coset_pattern_card (d : ℕ) : Fintype.card (CosetPattern d)=216^blockNumber (2^d) := by
  have cols : Fintype.card Colour=6 := by decide +kernel
  simp only [CosetPattern,Fintype.card_pi,cols,Fintype.card_coe,freeSlots_card,
    prod_const,card_univ,coset_blocks_card]
  norm_num

def cosetColours (d : ℕ) (hd : 6≤d) (c : CosetPattern d) : IncidenceColours (cubeRule (d+2)) :=
  fun B i => if act : B∈cosetBlocks d then if mem : i∈freeSlots B then c ⟨B,act⟩ ⟨i,mem⟩ else 1
    else cycleCoefficients (d+2) (by omega) B i

theorem coset_colour_at (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (B : cosetBlocks d) (i : freeSlots B.val) :
    cosetColours d hd c B.val i.val=c B i := by simp [cosetColours,B.prop,i.prop]

theorem coset_origin_colour (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (B : cosetBlocks d) :
    cosetColours d hd c B.val (blockOrigin B.val)=1 := by simp [cosetColours,B.prop,freeSlots]

theorem coset_colours_recovered (d : ℕ) (hd : 6≤d) (c e : CosetPattern d)
    (M : Matching (Cube (d+2))) (u v : CubeOffsets (d+2))
    (same : (colouredRule _ M (cosetColours d hd c) u).blocks=(colouredRule _ M (cosetColours d hd e) v).blocks) :
    c=e := by
  funext B i
  have eq := recover_coefficient M _ _ u v same B.val (blockOrigin_mem B.val) (mem_of_mem_erase i.prop)
    ((coset_origin_colour d hd c B).trans (coset_origin_colour d hd e B).symm)
  simpa only [coset_colour_at] using eq

theorem coset_colours_at_clean (d : ℕ) (hd : 6≤d) (c : CosetPattern d) {o : Cube (d+2)}
    (outside : o∉protectedSupport d (by omega)) (B : (cubeRule (d+2)).blocks) (inside : o∈B.val) (i : Cube (d+2)) :
    cosetColours d hd c B i=1 := by
  have bad : B∉cosetBlocks d := fun hit => outside (mem_union_left _ (coset_block_points d hit inside))
  rw [cosetColours,dif_neg bad]
  exact markedColour_outside _ _ (fun h => outside (mem_union_right _ h)) B inside i

theorem coset_plain (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (M : Matching (Cube (d+2)))
    (u : CubeOffsets (d+2)) {o : Cube (d+2)} (outside : o∉protectedSupport d (by omega)) :
    PlainThrough (colouredRule _ M (cosetColours d hd c) u) o := by
  apply plain_of_chart
  intro S inside
  unfold blockChart
  split
  · rename_i h
    funext i
    apply Equiv.ext
    intro x
    change move (cosetColours d hd c ⟨S,h⟩ i) x=x
    rw [coset_colours_at_clean d hd c outside _ inside i,move_one]
  · rfl

#print axioms blockOrigin
#print axioms blockOrigin_mem
#print axioms freeSlots
#print axioms freeSlots_card
#print axioms CosetPattern
#print axioms coset_pattern_card
#print axioms cosetColours
#print axioms coset_colour_at
#print axioms coset_origin_colour
#print axioms coset_colours_recovered
#print axioms coset_colours_at_clean
#print axioms coset_plain
end
end Erdos722.FourPoint
