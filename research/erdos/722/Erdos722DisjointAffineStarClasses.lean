import Erdos722AffineStarRigidity
import Erdos722LatinCosetClassCount

/-! # New asymmetric classes disjoint from every member of the coset construction -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
variable {d : ℕ} {hd : 6≤d}

local instance offsetFinite (L : Layout d hd) : Finite (OffsetClass L) :=
  Finite.of_surjective (QuotientAddGroup.mk : ExteriorOffsets L → OffsetClass L) QuotientAddGroup.mk_surjective

local instance choiceFintype (L : Layout d hd) : Fintype (Choices L) := by
  letI : Fintype (OffsetClass L) := Fintype.ofFinite _
  unfold Choices LocalChoices
  infer_instance

def starDesign (L : Layout d hd) (a : Choices L) := labelledBlocks (d+2) (starRule L a)
def starClass (L : Layout d hd) (a : Choices L) := classOf (starDesign L a)
def starClasses (L : Layout d hd) := univ.image (starClass L)

theorem starClass_injective (L : Layout d hd) : Function.Injective (starClass L) := by
  intro a b same
  change classOf (labelledBlocks _ (starRule L a))=classOf (labelledBlocks _ (starRule L b)) at same
  rw [class_eq_iff,labelledBlocks,labelledBlocks,relabel_iso_iff] at same
  obtain ⟨e,iso⟩ := same
  exact (star_isomorphism L a b e iso).1

theorem star_members (L : Layout d hd) (y) (h : y∈starClasses L) :
    ∃ D : Finset (Finset (Fin (4*2^(d+2)))), classOf D=y ∧ D.IsBlockDesign 3 4 ∧
      (binaryIncidence D).rank+(d+3)=4*2^(d+2) ∧ ∀ e : automorphisms D, e=1 := by
  obtain ⟨a,_,rfl⟩ := mem_image.mp h
  have rank := arbitrary_filling_rank (d+2) (rigidWord_top _ (by omega)) _ (star_compatible L a)
  refine ⟨starDesign L a,rfl,rank.1,rank.2,?_⟩
  let f := automorphismRelabel (fourLabels (d+2)) (starRule L a).blocks
  intro e
  obtain ⟨g,rfl⟩ := f.surjective e
  have id : g=1 := Subtype.ext (star_isomorphism L a a g.val g.prop).2
  change f g=1
  rw [id,map_one]

/-- The earlier coset family has at least two affine stars, even if all of its variable blocks are nonlinear. -/
theorem coset_two_stars (d : ℕ) (hd : 6≤d) (a : Parameters d) :
    ∃ i j : Base d, i≠j ∧ HasAffineStar (cubeRule (d+2)) (latinRule d hd a) i ∧
      HasAffineStar (cubeRule (d+2)) (latinRule d hd a) j := by
  let S := (univ : Finset (Base d)) \ cosetPoints d
  have room : 1<S.card := by
    rw [show S=univ \ cosetPoints d from rfl,card_sdiff_of_subset (subset_univ _),card_univ,coset_points_card]
    rw [show Fintype.card (Base d)=2^(d+2) by simp [Base,Cube],pow_add]
    have pos : 0<2^d := by positivity
    omega
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp room
  exact ⟨i,j,ne,coset_affine_star d hd a (mem_sdiff.mp hi).2,coset_affine_star d hd a (mem_sdiff.mp hj).2⟩

theorem disjoint_coset_classes (L : Layout d hd) : Disjoint (starClasses L) (latinClasses d hd) := by
  apply disjoint_left.mpr
  intro y hy hy'
  obtain ⟨a,_,rfl⟩ := mem_image.mp hy
  obtain ⟨b,_,eq⟩ := mem_image.mp hy'
  change classOf (labelledBlocks _ (latinRule d hd b))=classOf (labelledBlocks _ (starRule L a)) at eq
  rw [class_eq_iff,labelledBlocks,labelledBlocks,relabel_iso_iff] at eq
  obtain ⟨e,iso⟩ := eq
  have hyp : FibreHypotheses (cubeRule (d+2)) (matching d hd) :=
    ⟨cube_separates _,⟨0,edge_normalized 0 _⟩,(noFix_edge_iff ..).mpr (rigidWord_top _ (by omega))⟩
  obtain ⟨c⟩ := fibreMap_exists (latin_compatible d hd b) (star_compatible L a) hyp e iso
  obtain ⟨i,j,ne,hi,hj⟩ := coset_two_stars d hd b
  exact ne (c.base.injective ((unique_affine_root L a (map_affine_star c hi)).trans
    (unique_affine_root L a (map_affine_star c hj)).symm))

#print axioms offsetFinite
#print axioms choiceFintype
#print axioms starDesign
#print axioms starClass
#print axioms starClasses
#print axioms starClass_injective
#print axioms star_members
#print axioms coset_two_stars
#print axioms disjoint_coset_classes
end
end Erdos722.AffineStar
