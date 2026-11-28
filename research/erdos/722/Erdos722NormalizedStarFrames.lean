import Erdos722AffineStarTransport

/-! # The pair matchings at an intrinsically fixed point determine a common frame -/

namespace Erdos722.AffineStar
open Equiv Finset QuadCompletion FourPoint QuadSwitch
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]
variable {Q : Rule I} {M : Matching I} {P T : Rule (I × Fibre)} {e : Perm (I × Fibre)}

omit [DecidableEq I] [Fintype I] in
/-- The pair law alone coordinates all linear parts when the base map carries
a normalized matching star to a normalized matching star. -/
theorem normalized_frame (src : Compatible Q M P) (dst : Compatible Q M T)
    (c : FibreMap Q P T e) (o : I) (star : Normalized M o) (image : Normalized M (c.base o)) :
    ∃ s : Colour, Frame M M c.base s ∧ ∀ i x, c.fibre i x=move s x+c.fibre i 0 := by
  have pair (i j : I) (x : Fibre) :
      c.fibre j (move (M.transport i j) x)=
      c.fibre j 0+move (M.transport (c.base i) (c.base j)) (c.fibre i 0+c.fibre i x) := by
    have eq := c.commutes (i,0) (i,x) (j,0)
    rw [src.pair,c.point,c.point,c.point,c.point,dst.pair] at eq
    simpa only [zero_add] using congrArg Prod.snd eq
  obtain ⟨s,hs⟩ := affine_fibre (c.fibre o)
  have cancel (a b : Fibre) : a+(b+a)=b := (show ∀ a b : Fibre, a+(b+a)=b by decide +kernel) a b
  have lin (i : I) (x : Fibre) : c.fibre i x=move s x+c.fibre i 0 := by
    have eq := pair o i x
    rw [star,image,move_one,move_one,hs x,cancel,add_comm] at eq
    exact eq
  refine ⟨s,?_,lin⟩
  intro i j
  apply move_faithful
  intro x
  have eq := pair i j x
  rw [lin j _,lin i x,cancel,add_comm (c.fibre j 0)] at eq
  simpa only [move_product] using add_right_cancel eq

theorem translation_of_marked_star (src : Compatible Q M P) (dst : Compatible Q M T)
    (hyp : FibreHypotheses Q M) (rigid : Subsingleton (baseFrames Q M))
    (o : I) (norm : Normalized M o) (star : HasAffineStar Q P o)
    (unique : ∀ j, HasAffineStar Q T j → j=o)
    (iso : e.finsetCongr.finsetCongr P.blocks=T.blocks) :
    ∃ t : I → Fibre, e=pointForm 1 1 t := by
  obtain ⟨c⟩ := fibreMap_exists src dst hyp e iso
  have fixed := unique _ (map_affine_star c star)
  obtain ⟨s,frame,lin⟩ := normalized_frame src dst c o norm (by rwa [fixed])
  have one : (⟨(c.base,s),c.projects,frame⟩ : baseFrames Q M)=1 := rigid.elim _ _
  obtain ⟨hb,hs⟩ := Prod.mk.inj (show (c.base,s)=(1,1) from congrArg Subtype.val one)
  refine ⟨fun i => c.fibre i 0,Equiv.ext ?_⟩
  rintro ⟨i,x⟩
  rw [c.point,lin,hb,hs]
  rfl

#print axioms normalized_frame
#print axioms translation_of_marked_star
end
end Erdos722.AffineStar
