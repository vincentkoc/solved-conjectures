import Erdos722ExteriorOffsetQuotient
import Erdos722NormalizedStarFrames
import Erdos722AffineFallbackStars

/-! # Four-fibre Steiner quadruple systems with exactly one affine star -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
variable {d : ℕ} {hd : 6≤d}

abbrev Nonlinear := {q : Quasigroup // ¬AffineCube q}
abbrev FreeSites (L : Layout d hd) := interior L \ L.markers
abbrev LocalChoices (L : Layout d hd) := (L.markers → Nonlinear) × (FreeSites L → Quasigroup)
abbrev Choices (L : Layout d hd) := LocalChoices L × OffsetClass L

def localCube (L : Layout d hd) (a : LocalChoices L) (B : interior L) : Quasigroup :=
  if h : B.val∈L.markers then (a.1 ⟨B.val,h⟩).val else a.2 ⟨B.val,mem_sdiff.mpr ⟨B.prop,h⟩⟩

theorem localCube_injective (L : Layout d hd) : Function.Injective (localCube L) := by
  intro a b eq
  apply Prod.ext
  · funext B
    apply Subtype.ext
    have atB := congrFun eq (⟨B.val,L.marked B.prop⟩ : interior L)
    simpa only [localCube,dif_pos B.prop] using atB
  · funext B
    obtain ⟨inside,off⟩ := mem_sdiff.mp B.prop
    have atB := congrFun eq (⟨B.val,inside⟩ : interior L)
    simpa only [localCube,dif_neg off] using atB

def localLaw (L : Layout d hd) (a : LocalChoices L) : Laws (interior L) Fibre :=
  fun B => cubeLaw (blockOrder L B) symbols (localCube L a B)

abbrev fallback (L : Layout d hd) (a : OffsetClass L) :=
  colouredRule (cubeRule (d+2)) (matching d hd) (colours d hd) (outerOffset L a)

theorem fallback_compatible (L : Layout d hd) (a : OffsetClass L) :
    Compatible (cubeRule (d+2)) (matching d hd) (fallback L a) := blockwise_compatible ..

def starRule (L : Layout d hd) (a : Choices L) :=
  patch (cubeRule (d+2)) (fallback L a.2) (localLaw L a.1) (interior_size L) (fallback_compatible L a.2).project

theorem star_compatible (L : Layout d hd) (a : Choices L) :
    Compatible (cubeRule (d+2)) (matching d hd) (starRule L a) :=
  patch_compatible _ _ _ (fallback_compatible L a.2) _ _

theorem root_affine (L : Layout d hd) (a : Choices L) : HasAffineStar (cubeRule (d+2)) (starRule L a) 0 := by
  intro i j k ij ik jk inside
  have ext := L.pencil_sub (mem_filter.mpr ⟨completed_block _ ij ik jk,inside⟩)
  have off : baseQuad (cubeRule (d+2)) i j k ∉ interior L := fun h => (mem_sdiff.mp h).2 ext
  apply (off_graph _ (fallback L a.2) (localLaw L a.1) (interior_size L) (fallback_compatible L a.2).project off).mpr
  exact blockwise_closed _ _ (outerOffset L a.2) (linearCoordinates (colours d hd)) ij ik jk

theorem unique_affine_root (L : Layout d hd) (a : Choices L) {o : Base d}
    (star : HasAffineStar (cubeRule (d+2)) (starRule L a) o) : o=0 := by
  by_contra ne
  let Q := cubeRule (d+2)
  obtain ⟨B,mark,inside⟩ := L.cover o ne
  have block := (mem_sdiff.mp (L.marked mark)).1
  obtain ⟨i,j,k,hB⟩ := block_triple Q block
  have size : (insert (Q.complete i j k) {i,j,k} : Finset (Base d)).card=4 :=
    (congrArg Finset.card hB).trans (Q.isBlockDesign.1 B block)
  have tri : ({i,j,k} : Finset (Base d)).card=3 := by
    have t := @card_le_three (Base d) _ i j k
    have u := card_insert_le (Q.complete i j k) ({i,j,k} : Finset (Base d))
    omega
  obtain ⟨ij,ik,jk⟩ := card_triple_eq_three_iff.mp tri
  have closed := star i j k ij ik jk (hB ▸ inside)
  have m : baseQuad Q i j k∈interior L := hB ▸ L.marked mark
  have localClosed := (patch_closed_iff Q (fallback L a.2) (localLaw L a.1) (interior_size L)
    (fallback_compatible L a.2).project m).mp closed
  have affine := (cubeLaw_closed_iff (blockOrder L ⟨_,m⟩) (localCube L a.1 ⟨_,m⟩)).mp localClosed
  have marked : baseQuad Q i j k∈L.markers := hB ▸ mark
  rw [localCube,dif_pos marked] at affine
  exact (a.1.1 ⟨_,marked⟩).prop affine

theorem star_translation (L : Layout d hd) (a b : Choices L) (e : Perm (Base d × Fibre))
    (iso : e.finsetCongr.finsetCongr (starRule L a).blocks=(starRule L b).blocks) :
    ∃ t : Base d → Fibre, e=pointForm 1 1 t := by
  have hyp : FibreHypotheses (cubeRule (d+2)) (matching d hd) :=
    ⟨cube_separates _,⟨0,edge_normalized 0 _⟩,(noFix_edge_iff ..).mpr (rigidWord_top _ (by omega))⟩
  exact translation_of_marked_star (star_compatible L a) (star_compatible L b) hyp
    (path_word_frames _ (by omega)) 0 (edge_normalized 0 _) (root_affine L a)
    (fun _ => unique_affine_root L b) iso

#print axioms Nonlinear
#print axioms FreeSites
#print axioms LocalChoices
#print axioms Choices
#print axioms localCube
#print axioms localCube_injective
#print axioms localLaw
#print axioms fallback
#print axioms fallback_compatible
#print axioms starRule
#print axioms star_compatible
#print axioms root_affine
#print axioms unique_affine_root
#print axioms star_translation
end
end Erdos722.AffineStar
