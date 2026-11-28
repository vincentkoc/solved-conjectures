import Erdos722SparseMarkedIsomorphisms

/-! # Unrestricted isomorphisms between different compatible four-point fillings -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Equiv Finset
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- A common ordinary point after each possible base relabelling forces an
isomorphism to act by translations on the fibres. The two fillings can have
different local transversal codes. -/
theorem translation_between_fillings {Q : Rule I} {M : Matching I}
    {P T : Rule (I × Fibre)} (src : Compatible Q M P) (dst : Compatible Q M T)
    (hyp : FibreHypotheses Q M) (size : 3≤Fintype.card I) (rigid : Subsingleton (baseFrames Q M))
    (plain : ∀ b : Perm I, ∃ o, PlainThrough P o ∧ PlainThrough T (b o))
    (e : Perm (I × Fibre)) (h : e.finsetCongr.finsetCongr P.blocks=T.blocks) :
    ∃ t : I → Fibre, e=pointForm 1 1 t := by
  obtain ⟨root,star⟩ := hyp.star
  have same (i j : I) (x y : Fibre) : i=j ↔ (e (i,x)).1=(e (j,y)).1 := by
    have eq := sameChecks_relabel e P.blocks (i,x) (j,y)
    rw [show e.finsetCongr.finsetCongr P.blocks=T.blocks from h] at eq
    exact (sameChecks_four hyp.separates src star hyp.noFix _ _).symm.trans
      (eq.trans (sameChecks_four hyp.separates dst star hyp.noFix _ _))
  obtain ⟨b,f,coord⟩ := fibre_coordinates 0 e same
  have ec (p : I × Fibre) : e p=(b p.1,f p.1 p.2) := coord p.1 p.2
  have comp (i j k : I) (x y z : Fibre) :
      (b (Q.complete i j k),f (Q.complete i j k) (P.complete (i,x) (j,y) (k,z)).2)=
      T.complete (b i,f i x) (b j,f j y) (b k,f k z) := by
    have eq := completion_of_blocks P T e h (i,x) (j,y) (k,z)
    rwa [ec (P.complete ..),src.project,coord,coord,coord] at eq
  obtain ⟨o,hp,ht⟩ := plain b
  obtain ⟨s,frame,lin⟩ := frame_at_plain_point src dst o size hp ht
    (fun i j k x y z => congrArg Prod.snd (comp i j k x y z))
  have base (i j k : I) : b (Q.complete i j k)=Q.complete (b i) (b j) (b k) :=
    (congrArg Prod.fst (comp i j k 0 0 0)).trans (dst.project ..)
  have one : (⟨(b,s),base,frame⟩ : baseFrames Q M)=1 := rigid.elim _ _
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (show (b,s)=(1,1) from congrArg Subtype.val one)
  have form : e=pointForm 1 1 (fun i => f i 0) := by
    apply Equiv.ext
    rintro ⟨i,x⟩
    rw [coord,lin]
    rfl
  exact ⟨_,form⟩

#print axioms translation_between_fillings
end
end Erdos722.FourPoint
