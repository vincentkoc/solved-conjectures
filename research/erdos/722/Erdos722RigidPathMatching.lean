import Erdos722RigidMatchingPath
import Erdos722FourFibreLabelled
import Erdos722FourFibreGroups

/-! # An explicit normalized matching array with trivial base-colour stabilizer -/

namespace Erdos722.FourPoint
open QuadCompletion Equiv

def pathSwap : Colour := Equiv.swap 0 1

private def kind (s : Colour) : ℕ := if s=1 then 1 else if s*s=1 then 2 else 3

private theorem kind_eq : ∀ s a b : Colour, s*a=b*s → kind a=kind b := by decide +kernel

private theorem kinds : kind 1=1 ∧ kind pathSwap=2 ∧ kind threeCycle=3 ∧ kind threeCycle⁻¹=3 := by
  decide +kernel

private theorem central : ∀ s : Colour, s*pathSwap=pathSwap*s → s*threeCycle=threeCycle*s → s=1 := by
  decide +kernel

def pathColour (i j : ℕ) : Colour :=
  if pathTag i j=1 then 1 else if pathTag i j=2 then pathSwap
  else if i<j then threeCycle else threeCycle⁻¹

private theorem tag_kind (i j : ℕ) : kind (pathColour i j)=pathTag i j := by
  have h : pathTag i j=1 ∨ pathTag i j=2 ∨ pathTag i j=3 := by unfold pathTag; split_ifs <;> omega
  rcases h with h|h|h
  · simpa only [pathColour,if_pos h] using kinds.1.trans h.symm
  · simp only [pathColour,h,↓reduceIte]; exact kinds.2.1
  · by_cases l : i<j <;> simp [pathColour,h,l,kinds.2.2.1,kinds.2.2.2]

private theorem path_reverse (i j : ℕ) : pathColour j i=(pathColour i j)⁻¹ := by
  by_cases eq : i=j
  · subst j; simp [pathColour,(pathTag_one i i).mpr (by simp)]
  unfold pathColour
  rw [pathTag_symm j i]
  by_cases a : pathTag i j=1
  · simp [a]
  by_cases b : pathTag i j=2
  · simp [b,pathSwap]
  rcases lt_or_gt_of_ne eq with l|l <;> simp [a,b,l,not_lt_of_ge l.le]

def pathMatching {I : Type*} {m : ℕ} (e : I ≃ Fin (m+4)) : Matching I where
  transport i j := pathColour (e i).val (e j).val
  diagonal i := by
    have h := (pathTag_one (e i).val (e i).val).mpr (Or.inr (Or.inr (Or.inl rfl)))
    simp only [pathColour,if_pos h]
  reverse i j := path_reverse ..

theorem path_star {I : Type*} {m : ℕ} (e : I ≃ Fin (m+4)) :
    Normalized (pathMatching e) (e.symm ⟨0,by omega⟩) := by
  intro i
  simp [pathMatching,pathColour,(pathTag_one 0 (e i).val).mpr (Or.inl rfl)]

private theorem chord : pathColour 1 3=threeCycle := by decide +kernel
private theorem adjacent : pathColour 2 3=pathSwap := by decide +kernel

theorem path_noFix {I : Type*} {m : ℕ} (e : I ≃ Fin (m+4)) :
    ¬∃ d : Direction, ∀ i j, (pathMatching e).transport i j d=d := by
  rintro ⟨d,h⟩
  apply cycle_free d
  simpa only [pathMatching,Equiv.apply_symm_apply,chord] using
    h (e.symm ⟨1,by omega⟩) (e.symm ⟨3,by omega⟩)

theorem path_frame_trivial {I : Type*} {m : ℕ} (e : I ≃ Fin (m+4)) (Q : Rule I)
    (g : baseFrames Q (pathMatching e)) : g=1 := by
  let p := e.permCongr g.val.1
  have tags (i j : Fin (m+4)) : pathTag (p i).val (p j).val=pathTag i.val j.val := by
    have eq := (kind_eq _ _ _ (g.prop.2 (e.symm i) (e.symm j))).symm
    simpa only [pathMatching,Equiv.apply_symm_apply,tag_kind,p,Equiv.permCongr_apply] using eq
  have root : g.val.1=1 := by
    have eq := pathTag_rigid m p tags
    apply Equiv.ext
    intro i
    apply e.injective
    simpa only [p,Equiv.permCongr_apply,Equiv.symm_apply_apply,Equiv.Perm.one_apply] using
      DFunLike.congr_fun eq (e i)
  have comm (i j : Fin (m+4)) :
      g.val.2*pathColour i.val j.val=pathColour i.val j.val*g.val.2 := by
    have eq := g.prop.2 (e.symm i) (e.symm j)
    simpa only [root,Equiv.Perm.one_apply,pathMatching,Equiv.apply_symm_apply] using eq
  have colour : g.val.2=1 := central _ (by simpa only [adjacent] using comm ⟨2,by omega⟩ ⟨3,by omega⟩)
    (by simpa only [chord] using comm ⟨1,by omega⟩ ⟨3,by omega⟩)
  exact Subtype.ext (Prod.ext root colour)

#print axioms pathSwap
#print axioms pathColour
#print axioms pathMatching
#print axioms path_star
#print axioms path_noFix
#print axioms path_frame_trivial
end Erdos722.FourPoint
