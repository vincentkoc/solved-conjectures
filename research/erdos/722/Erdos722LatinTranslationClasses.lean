import Erdos722LatinParameterRecovery
import Erdos722ExteriorTranslationKernel

/-! # The free fibre-translation action on arbitrary local Latin cubes -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

def symbolShift (d : ℕ) (B : region d) (t : Base d → Fibre) (j : Symbol) : Perm Symbol :=
  (symbols.symm.trans (Equiv.addRight (t ((numbering d B j).val)))).trans symbols

def shiftParameters (d : ℕ) (hd : 6≤d) (a : Parameters d) (t : Base d → Fibre) : Parameters d :=
  (fun B => relabel (a.1 B) (symbolShift d B t), a.2+exteriorGradient d hd t)

private theorem shift_local (d : ℕ) (hd : 6≤d) (a : Parameters d) (t : Base d → Fibre)
    (B : region d) (f : Base d → Fibre) (h : (laws d a.1 B).accepts f) :
    (laws d (shiftParameters d hd a t).1 B).accepts (fun i => f i+t i) := by
  have eq := (graph_relabel (a.1 B) (symbolShift d B t) (fun j => symbols (f (numbering d B j).val))).mpr h
  change graph (relabel (a.1 B) (symbolShift d B t)) (fun j => symbols (f (numbering d B j).val+t (numbering d B j).val))
  have vec : (fun j => symbolShift d B t j (symbols (f (numbering d B j).val))) =
      (fun j => symbols (f (numbering d B j).val+t (numbering d B j).val)) := by
    funext j
    change symbols (symbols.symm (symbols (f (numbering d B j).val)) + t (numbering d B j).val) = _
    rw [symbols.symm_apply_apply]
  rw [vec] at eq
  exact eq

private theorem shift_offset (d : ℕ) (hd : 6≤d) (a : Parameters d) (t : Base d → Fibre)
    (i j k : Base d) (off : baseQuad (cubeRule (d+2)) i j k∉region d) :
    transversalOffset (cubeRule (d+2)) (extendOffset d a.2+weightedGradient _ (colours d hd) t) i j k=
    transversalOffset (cubeRule (d+2)) (extendOffset d (shiftParameters d hd a t).2) i j k := by
  let Q := cubeRule (d+2)
  let B := baseQuad Q i j k
  change offsetAt Q _ B=offsetAt Q _ B
  by_cases h : B∈Q.blocks
  · have outer : B∈outsideBlocks d := mem_sdiff.mpr ⟨h,off⟩
    simp only [offsetAt,dif_pos h,Pi.add_apply,extendOffset,dif_pos outer]
    rfl
  · simp only [offsetAt,dif_neg h]

private theorem shift_point {I : Type*} (t : I → Fibre) (x : I × Fibre) :
    pointForm (1 : Perm I) 1 t x=movePoint (fun i => Equiv.addRight (t i)) x := by
  simp [pointForm,movePoint,move_one]

theorem shifted_blocks (d : ℕ) (hd : 6≤d) (a : Parameters d) (t : Base d → Fibre) :
    (pointForm (1 : Perm (Base d)) 1 t).finsetCongr.finsetCongr (latinRule d hd a).blocks=
      (latinRule d hd (shiftParameters d hd a t)).blocks := by
  let Q := cubeRule (d+2)
  let M := matching d hd
  let C := colours d hd
  let u := extendOffset d a.2
  let G := weightedGradient Q C t
  let b := shiftParameters d hd a t
  let T := colouredRule Q M C (u+G)
  let e := pointForm (1 : Perm (Base d)) 1 t
  have trans := completion_of_blocks (baseline d hd a.2) T e (translation_coloured_blocks M C u t)
  apply blocks_of_completion
  intro x y z
  simp only [shift_point]
  apply patch_transport Q (baseline d hd a.2) (baseline d hd b.2) (laws d a.1) (laws d b.1)
    (region_size d) (baseline_compatible d hd _).project (baseline_compatible d hd _).project
    (fun i => Equiv.addRight (t i)) (shift_local d hd a t) _ x y z
  rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ off
  have eq := trans (i,x) (j,y) (k,z)
  have coord (v : Base d × Fibre) : e v=movePoint (fun i => Equiv.addRight (t i)) v := shift_point ..
  simp only [coord] at eq
  exact eq.trans (coloured_eq_at Q M C (u+G) (extendOffset d b.2) i j k _ _ _
    (shift_offset d hd a t _ _ _ off))

theorem shift_injective (d : ℕ) (hd : 6≤d) (a : Parameters d) : Function.Injective (shiftParameters d hd a) := by
  intro t u h
  exact exterior_injective d hd (add_left_cancel (a:=a.2) (congrArg Prod.snd h))

theorem latin_class_iff (d : ℕ) (hd : 6≤d) (a b : Parameters d) :
    classOf (latinDesign d hd a)=classOf (latinDesign d hd b) ↔
      ∃ t : Base d → Fibre, shiftParameters d hd a t=b := by
  rw [class_eq_iff,latinDesign,latinDesign,labelledBlocks,labelledBlocks,relabel_iso_iff]
  constructor
  · rintro ⟨e,h⟩
    obtain ⟨t,rfl⟩ := iso_translation d hd a b e h
    exact ⟨t,parameters_recovered d hd _ _ ((shifted_blocks d hd a t).symm.trans h)⟩
  · rintro ⟨t,rfl⟩
    exact ⟨_,shifted_blocks d hd a t⟩

theorem latin_asymmetric (d : ℕ) (hd : 6≤d) (a : Parameters d)
    (e : automorphisms (latinDesign d hd a)) : e=1 := by
  let R := latinRule d hd a
  let L := automorphismRelabel (fourLabels (d+2)) R.blocks
  obtain ⟨f,rfl⟩ := L.surjective e
  obtain ⟨t,form⟩ := iso_translation d hd a a f.val f.prop
  have hit := f.prop
  rw [form] at hit
  have same := parameters_recovered d hd _ _ ((shifted_blocks d hd a t).symm.trans hit)
  have off : a.2+exteriorGradient d hd t=a.2 := congrArg Prod.snd same
  have z := exterior_kernel d hd t (add_left_cancel (a:=a.2) (off.trans (add_zero a.2).symm))
  have one : f=1 := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨i,x⟩
    change f.val (i,x)=(i,x)
    rw [form,z,shift_point]
    change (i,x+0)=(i,x)
    rw [add_zero]
  change L f=1
  rw [one,map_one]

#print axioms symbolShift
#print axioms shiftParameters
#print axioms shifted_blocks
#print axioms shift_injective
#print axioms latin_class_iff
#print axioms latin_asymmetric
end
end Erdos722.LatinFillings
