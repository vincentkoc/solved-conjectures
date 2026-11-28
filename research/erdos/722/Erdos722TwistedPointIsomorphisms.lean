import Erdos722TwistedFibreFrame

/-! # Unrestricted point isomorphisms of translated four-fibre fillings -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Equiv
variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]

/-- Equating the constants in the transversal completion identity includes
repeated fibres, whose two identical translations cancel. -/
def OffsetLaw (Q : Rule I) (R : Rule J) (u : BlockOffsets Q) (v : BlockOffsets R)
    (b : I ≃ J) (s : Colour) (t : I → Fibre) : Prop :=
  ∀ i j k, move s (transversalOffset Q u i j k)+t (Q.complete i j k)=
    t i+t j+t k+transversalOffset R v (b i) (b j) (b k)

theorem twisted_iso_iff {Q : Rule I} {R : Rule J} {M : Matching I} {N : Matching J}
    (src : FibreHypotheses Q M) (dst : FibreHypotheses R N) (size : 3≤Fintype.card I)
    (u : BlockOffsets Q) (v : BlockOffsets R) (e : I × Fibre ≃ J × Fibre) :
    e.finsetCongr.finsetCongr (twistedRule Q M u).blocks=(twistedRule R N v).blocks ↔
    ∃ (b : I ≃ J) (s : Colour) (t : I → Fibre),
      (∀ i j k, b (Q.complete i j k)=R.complete (b i) (b j) (b k)) ∧
      Frame M N b s ∧ OffsetLaw Q R u v b s t ∧ e=pointForm b s t := by
  constructor
  · intro h
    obtain ⟨o,ho⟩ := src.star
    obtain ⟨p,hp⟩ := dst.star
    have same (i j : I) (x y : Fibre) : i=j ↔ (e (i,x)).1=(e (j,y)).1 := by
      have eq := sameChecks_relabel e (twistedRule Q M u).blocks (i,x) (j,y)
      rw [h] at eq
      exact (sameChecks_four src.separates (twisted_compatible ..) ho src.noFix _ _).symm.trans
        (eq.trans (sameChecks_four dst.separates (twisted_compatible ..) hp dst.noFix _ _))
    obtain ⟨b,f,coord⟩ := fibre_coordinates 0 e same
    have comp (i j k : I) (x y z : Fibre) :
        (b (Q.complete i j k),f (Q.complete i j k) (twistedFourth Q M u i j k x y z))=
        (R.complete (b i) (b j) (b k),twistedFourth R N v (b i) (b j) (b k) (f i x) (f j y) (f k z)) := by
      have eq := completion_of_blocks _ _ e h (i,x) (j,y) (k,z)
      change e (Q.complete i j k,twistedFourth Q M u i j k x y z)=_ at eq
      simpa only [coord,twistedRule] using eq
    have law : TwistedLaw Q R M N u v b f := fun i j k x y z => congrArg Prod.snd (comp i j k x y z)
    obtain ⟨s,frame,lin⟩ := twisted_frame size o law
    refine ⟨b,s,fun i => f i 0,fun i j k => congrArg Prod.fst (comp i j k 0 0 0),frame,?_,?_⟩
    · intro i j k
      have eq := law i j k 0 0 0
      have tr := translate_fourth N (fun j => f (b.symm j) 0) (b i) (b j) (b k) 0 0 0
      have z (P : Matching I) (a b c : I) : fourth P a b c 0 0 0=0 := by simp [fourth,move_zero]
      have z' (a b c : J) : fourth N a b c 0 0 0=0 := by simp [fourth,move_zero]
      simp only [b.symm_apply_apply,zero_add,z'] at tr
      simp only [twistedFourth,z,zero_add,tr] at eq
      rwa [lin (Q.complete i j k) _] at eq
    · apply Equiv.ext
      rintro ⟨i,x⟩
      rw [coord,lin i x]
      rfl
  · rintro ⟨b,s,t,base,frame,shift,rfl⟩
    apply blocks_of_completion
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩
    refine Prod.ext (base i j k) ?_
    change move s (twistedFourth Q M u i j k x y z)+t (Q.complete i j k)=
      twistedFourth R N v (b i) (b j) (b k) (move s x+t i) (move s y+t j) (move s z+t k)
    have tr := translate_fourth N (fun j => t (b.symm j)) (b i) (b j) (b k) (move s x) (move s y) (move s z)
    simp only [b.symm_apply_apply] at tr
    rw [twistedFourth,twistedFourth,move_add,map_fourth frame,tr,add_assoc,shift]
    ac_rfl

#print axioms OffsetLaw
#print axioms twisted_iso_iff
end Erdos722.FourPoint
