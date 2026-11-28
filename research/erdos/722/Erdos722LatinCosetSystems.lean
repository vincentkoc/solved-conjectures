import Erdos722TransversalReplacement
import Erdos722CosetAsymmetricCount

/-! # Matched Steiner quadruple systems with unrestricted Latin cubes on a binary coset -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev Base (d : ℕ) := Cube (d+2)

def region (d : ℕ) : Finset (Finset (Base d)) := (cosetBlocks d).image Subtype.val

theorem region_mem (d : ℕ) (B : (cubeRule (d+2)).blocks) : B.val ∈ region d ↔ B ∈ cosetBlocks d := by
  simp [region]

theorem region_sub (d : ℕ) : region d ⊆ (cubeRule (d+2)).blocks := by
  intro B h
  obtain ⟨b,_,rfl⟩ := mem_image.mp h
  exact b.prop

theorem region_size (d : ℕ) (B) (h : B∈region d) : B.card=4 :=
  (((cubeRule (d+2)).mem_blocks B).mp (region_sub d h)).1

theorem region_card (d : ℕ) : (region d).card=blockNumber (2^d) := by
  rw [region,card_image_of_injective _ Subtype.val_injective,coset_blocks_card]

theorem region_points (d : ℕ) {B : Finset (Base d)} (h : B ∈ region d) : B ⊆ cosetPoints d := by
  obtain ⟨b,hb,rfl⟩ := mem_image.mp h
  exact coset_block_points d hb

def outsideBlocks (d : ℕ) := (cubeRule (d+2)).blocks \ region d

theorem outside_card (d : ℕ) : (outsideBlocks d).card=
    blockNumber (2^(d+2))-blockNumber (2^d) := by
  rw [outsideBlocks,card_sdiff_of_subset (region_sub d),region_card,base_block_count (cubeRule (d+2)).isBlockDesign]
  simp [blockNumber,Cube]

def numbering (d : ℕ) (B : region d) : Symbol ≃ B.val :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,region_size d B.val B.prop])).symm

def symbols : Fibre ≃ Symbol := Fintype.equivFinOfCardEq (by simp [Fibre])

abbrev Fillings (d : ℕ) := region d → Quasigroup
abbrev OutsideOffsets (d : ℕ) := outsideBlocks d → Fibre
abbrev Parameters (d : ℕ) := Fillings d × OutsideOffsets d

def laws (d : ℕ) (c : Fillings d) : Laws (region d) Fibre :=
  fun B => cubeLaw (numbering d B) symbols (c B)

def extendOffset (d : ℕ) (u : OutsideOffsets d) : CubeOffsets (d+2) :=
  fun B => if h : B.val ∈ outsideBlocks d then u ⟨B.val,h⟩ else 0

abbrev colours (d : ℕ) (hd : 6≤d) := cycleCoefficients (d+2) (by omega)
abbrev matching (d : ℕ) (hd : 6≤d) := markedMatching (d+2) (by omega)
abbrev baseline (d : ℕ) (hd : 6≤d) (u : OutsideOffsets d) :=
  colouredRule (cubeRule (d+2)) (matching d hd) (colours d hd) (extendOffset d u)

theorem baseline_compatible (d : ℕ) (hd : 6≤d) (u : OutsideOffsets d) :
    Compatible (cubeRule (d+2)) (matching d hd) (baseline d hd u) := blockwise_compatible ..

def latinRule (d : ℕ) (hd : 6≤d) (a : Parameters d) :=
  patch (cubeRule (d+2)) (baseline d hd a.2) (laws d a.1) (region_size d) (baseline_compatible d hd a.2).project

theorem latin_compatible (d : ℕ) (hd : 6≤d) (a : Parameters d) :
    Compatible (cubeRule (d+2)) (matching d hd) (latinRule d hd a) :=
  patch_compatible _ _ _ (baseline_compatible d hd a.2) _ _

def latinDesign (d : ℕ) (hd : 6≤d) (a : Parameters d) := labelledBlocks (d+2) (latinRule d hd a)

theorem latin_design_rank (d : ℕ) (hd : 6≤d) (a : Parameters d) :
    (latinDesign d hd a).IsBlockDesign 3 4 ∧
      (binaryIncidence (latinDesign d hd a)).rank + (d+3)=4*2^(d+2) :=
  arbitrary_filling_rank (d+2) (rigidWord_top _ (by omega)) _ (latin_compatible d hd a)

/-- The ordinary through-triples are preserved wherever the point avoids the variable and marked supports. -/
theorem latin_plain (d : ℕ) (hd : 6≤d) (a : Parameters d) {o : Base d}
    (clean : o ∉ protectedSupport d (by omega)) : PlainThrough (latinRule d hd a) o := by
  have point : o ∉ cosetPoints d := fun h => clean (mem_union_left _ h)
  have plain : PlainThrough (baseline d hd a.2) o := by
    apply plain_of_chart
    intro S inside
    unfold blockChart
    split
    · rename_i h
      funext i
      apply Equiv.ext
      intro x
      change move (colours d hd ⟨S,h⟩ i) x=x
      have same := markedColour_outside (cubePrivateBlocks (d+2) (by omega)) (fun _ => threeCycle)
        (fun h => clean (mem_union_right _ h)) ⟨S,h⟩ inside i
      rw [show colours d hd ⟨S,h⟩ i=1 from same,move_one]
    · rfl
  intro i k io ik ok
  obtain ⟨v,hv⟩ := plain i k io ik ok
  refine ⟨v,fun x y z => ?_⟩
  have off : baseQuad (cubeRule (d+2)) i o k ∉ region d :=
    fun h => point (region_points d h (by simp [baseQuad]))
  exact (congrArg Prod.snd (patch_outside _ _ _ _ _ (i,x) (o,y) (k,z) off)).trans (hv x y z)

theorem iso_translation (d : ℕ) (hd : 6≤d) (a b : Parameters d) (e : Perm (Base d × Fibre))
    (iso : e.finsetCongr.finsetCongr (latinRule d hd a).blocks=(latinRule d hd b).blocks) :
    ∃ t : Base d → Fibre, e=pointForm 1 1 t := by
  have hyp : FibreHypotheses (cubeRule (d+2)) (matching d hd) :=
    ⟨cube_separates _,⟨0,edge_normalized 0 _⟩,(noFix_edge_iff ..).mpr (rigidWord_top _ (by omega))⟩
  have size : 3≤Fintype.card (Base d) := by
    simpa [Base,Cube] using (show 3≤2^(d+2) by have := sparse_basis_size (by omega : 6≤d+2); omega)
  apply translation_between_fillings (latin_compatible d hd a) (latin_compatible d hd b)
    hyp size (path_word_frames (d+2) (by omega)) _ e iso
  intro g
  obtain ⟨o,p,q⟩ := coset_common_anchor d hd g
  exact ⟨o,latin_plain d hd a p,latin_plain d hd b q⟩

#print axioms Base
#print axioms region
#print axioms region_mem
#print axioms region_sub
#print axioms region_size
#print axioms region_card
#print axioms region_points
#print axioms outsideBlocks
#print axioms outside_card
#print axioms numbering
#print axioms symbols
#print axioms Fillings
#print axioms OutsideOffsets
#print axioms Parameters
#print axioms laws
#print axioms extendOffset
#print axioms colours
#print axioms matching
#print axioms baseline
#print axioms baseline_compatible
#print axioms latinRule
#print axioms latin_compatible
#print axioms latinDesign
#print axioms latin_design_rank
#print axioms latin_plain
#print axioms iso_translation
end
end Erdos722.LatinFillings
