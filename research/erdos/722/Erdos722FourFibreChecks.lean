import Erdos722FourFibreRule
import Erdos722CompletionParity

/-! # Restriction of binary parity checks to the four-point fibres -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- The projection and pair identities leave the transversal fillings unrestricted. -/
structure Compatible (Q : Rule I) (M : Matching I) (R : Rule (I × Fibre)) : Prop where
  project (a b c) : (R.complete a b c).1=Q.complete a.1 b.1 c.1
  pair (i j x y z) : R.complete (i,x) (i,y) (j,z)=(j,z+move (M.transport i j) (x+y))

omit [Fintype I] in
theorem fourRule_compatible (Q : Rule I) (M : Matching I) :
    Compatible Q M (fourRule Q M) where
  project _ _ _ := rfl
  pair _ _ _ _ _ := Prod.ext (Q.repeated ..) (by simp [fourRule,fourth])

/-- A star of identity matchings fixes a common set of direction labels. -/
def Normalized (M : Matching I) (o : I) := ∀ i, M.transport o i=1

abbrev Invariant (M : Matching I) :=
  {c : Option Direction // ∀ i j, c.map (M.transport i j)=c}

theorem restrict_check {Q : Rule I} {M : Matching I} {R : Rule (I × Fibre)}
    (compat : Compatible Q M R) {o : I} (star : Normalized M o) (u : Checks R.blocks) :
    ∃ c : Invariant M, ∀ i x, u.val (i,x)=u.val (i,0)+character c.val x := by
  let g (x : Fibre) := u.val (o,x)+u.val (o,0)
  have hom := (check_iff_complete R _).mp u.prop
  have step (i : I) (x z : Fibre) : u.val (i,z+x)=g x+u.val (i,z) := by
    have h := hom (o,x) (o,0) (i,z)
    rwa [compat.pair,star i,move_one,add_zero] at h
  have decomp (i : I) (x : Fibre) : u.val (i,x)=u.val (i,0)+g x := by
    simpa only [zero_add,add_comm (g x)] using step i x 0
  have gz : g 0=0 := CharTwo.add_self_eq_zero _
  have ga (x y : Fibre) : g (x+y)=g x+g y := by
    change u.val (o,x+y)+u.val (o,0)=_
    rw [step,add_assoc,add_comm (g x)]
  obtain ⟨c,hc⟩ := character_exists g gz ga
  refine ⟨⟨c,?_⟩,by simpa only [hc] using decomp⟩
  intro i j
  apply (character_move ..).mp
  intro x
  have h := hom (i,x) (i,0) (j,0)
  rw [compat.pair,zero_add,add_zero,decomp j,decomp i x] at h
  simp only [hc]
  exact (show ∀ a b p q : ZMod 2, a+p=b+q+b+a → p=q by decide) _ _ _ _ h

/-- If the edge permutations have no common fixed direction, all checks descend,
for any compatible choice of transversal fillings. -/
noncomputable def descendedChecks {Q : Rule I} {M : Matching I} {R : Rule (I × Fibre)}
    (compat : Compatible Q M R) {o : I} (star : Normalized M o)
    (noFix : ¬∃ d : Direction, ∀ i j, M.transport i j d=d) : Checks Q.blocks ≃ Checks R.blocks := by
  let lift (u : Checks Q.blocks) : Checks R.blocks :=
    ⟨fun p => u.val p.1,(check_iff_complete R _).mpr fun a b c => by
      simpa only [compat.project] using (check_iff_complete Q _).mp u.prop a.1 b.1 c.1⟩
  apply Equiv.ofBijective lift
  constructor
  · intro u v h
    exact Subtype.ext (funext fun i => congrArg (fun t : Checks R.blocks => t.val (i,0)) h)
  · intro u
    obtain ⟨⟨c,inv⟩,hu⟩ := restrict_check compat star u
    cases c with
    | some d => exact (noFix ⟨d,fun i j => Option.some.inj (inv i j)⟩).elim
    | none =>
      have h (i x) : u.val (i,x)=u.val (i,0) := by simpa [character] using hu i x
      refine ⟨⟨fun i => u.val (i,0),(check_iff_complete Q _).mpr ?_⟩,
        Subtype.ext (funext fun p => (h p.1 p.2).symm)⟩
      intro a b c
      let p := R.complete (a,0) (b,0) (c,0)
      have hp : p.1=Q.complete a b c := compat.project ..
      have base := (check_iff_complete R _).mp u.prop (a,0) (b,0) (c,0)
      exact (congrArg (fun i => u.val (i,0)) hp.symm).trans ((h p.1 p.2).symm.trans base)

#print axioms Compatible
#print axioms fourRule_compatible
#print axioms Normalized
#print axioms Invariant
#print axioms restrict_check
#print axioms descendedChecks
end Erdos722.FourPoint
