import Erdos722FourFibreFrame

/-! # Classification of block isomorphisms of split four-fibre systems -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Equiv
variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]

structure FibreHypotheses (Q : Rule I) (M : Matching I) : Prop where
  separates : Separates Q.blocks
  star : ∃ o, Normalized M o
  noFix : ¬∃ d : Direction, ∀ i j, M.transport i j d=d

/-- The base map, a single colour, and a check-valued translation describe
every isomorphism of the actual block sets. The criterion allows the base
points and the distinguished normalization stars to move. -/
theorem four_fibre_iso_iff {Q : Rule I} {R : Rule J} {M : Matching I} {N : Matching J}
    (src : FibreHypotheses Q M) (dst : FibreHypotheses R N) (size : 3≤Fintype.card I)
    (e : I × Fibre ≃ J × Fibre) :
    e.finsetCongr.finsetCongr (fourRule Q M).blocks=(fourRule R N).blocks ↔
    ∃ (b : I ≃ J) (s : Colour) (t : I → Fibre),
      (∀ i j k, b (Q.complete i j k)=R.complete (b i) (b j) (b k)) ∧
      Frame M N b s ∧ Offset Q t ∧ e=pointForm b s t := by
  constructor
  · intro h
    obtain ⟨o,ho⟩ := src.star
    obtain ⟨p,hp⟩ := dst.star
    have same (i j : I) (x y : Fibre) : i=j ↔ (e (i,x)).1=(e (j,y)).1 := by
      have eq := sameChecks_relabel e (fourRule Q M).blocks (i,x) (j,y)
      rw [h] at eq
      exact (sameChecks_four src.separates (fourRule_compatible ..) ho src.noFix _ _).symm.trans
        (eq.trans (sameChecks_four dst.separates (fourRule_compatible ..) hp dst.noFix _ _))
    obtain ⟨b,v,coord⟩ := fibre_coordinates 0 e same
    have comp (i j k : I) (x y z : Fibre) :
        (b (Q.complete i j k),v (Q.complete i j k) (fourth M i j k x y z))=
        (R.complete (b i) (b j) (b k),fourth N (b i) (b j) (b k) (v i x) (v j y) (v k z)) := by
      have eq := completion_of_blocks _ _ e h (i,x) (j,y) (k,z)
      change e (Q.complete i j k,fourth M i j k x y z)=_ at eq
      simpa only [coord,fourRule] using eq
    have law : FibreLaw Q M N b v := fun i j k x y z => congrArg Prod.snd (comp i j k x y z)
    obtain ⟨s,lin⟩ := common_colour size o law
    refine ⟨b,s,fun i => v i 0,fun i j k => congrArg Prod.fst (comp i j k 0 0 0),
      frame_of_law law lin,offset_of_law law,?_⟩
    apply Equiv.ext
    rintro ⟨i,x⟩
    rw [coord,lin i x]
    rfl
  · rintro ⟨b,s,t,base,frame,shift,rfl⟩
    exact form_preserves base frame shift

omit [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J] in
theorem pointForm_unique (o : I) {b c : I ≃ J} {s r : Colour} {t u : I → Fibre}
    (h : pointForm b s t=pointForm c r u) : b=c ∧ s=r ∧ t=u := by
  have ev (i : I) (x : Fibre) := DFunLike.congr_fun h (i,x)
  have base : b=c := Equiv.ext fun i => congrArg Prod.fst (ev i 0)
  have shift : t=u := funext fun i => by
    simpa only [pointForm,Equiv.coe_fn_mk,move_zero,zero_add] using congrArg Prod.snd (ev i 0)
  subst u
  refine ⟨base,move_faithful fun x => ?_,rfl⟩
  exact add_right_cancel (show move s x+t o=move r x+t o from congrArg Prod.snd (ev o x))

#print axioms FibreHypotheses
#print axioms four_fibre_iso_iff
#print axioms pointForm_unique
end Erdos722.FourPoint
