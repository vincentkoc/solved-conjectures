import Erdos722FourFibreChecks

/-! # Exact parity checks when the transversal fibre coordinates sum to zero -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch
variable {I : Type*} [DecidableEq I] [Fintype I]

omit [Fintype I] in
private theorem character_fourth (M : Matching I) (v : Invariant M) (i j k : I) (x y z : Fibre) :
    character v.val (fourth M i j k x y z)=character v.val x+character v.val y+character v.val z := by
  have move_eq (a b t) := (character_move _ _).mpr (v.prop a b) t
  unfold fourth
  split_ifs <;> simp only [character_add,move_eq] <;> ac_rfl

/-- A base check and one invariant fibre character give every check exactly once. -/
noncomputable def splitChecks (Q : Rule I) (M : Matching I) {o : I} (star : Normalized M o) :
    Checks Q.blocks × Invariant M ≃ Checks (fourRule Q M).blocks := by
  let f (v : Checks Q.blocks × Invariant M) : Checks (fourRule Q M).blocks :=
    ⟨fun p => v.1.val p.1+character v.2.val p.2,(check_iff_complete _ _).mpr fun a b c => by
      change v.1.val (Q.complete ..)+character v.2.val (fourth ..)=_
      rw [(check_iff_complete Q _).mp v.1.prop,character_fourth M v.2]
      ac_rfl⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨u,c⟩ ⟨v,b⟩ he
    have ev (i : I) (x : Fibre) := congrArg (fun p : Checks (fourRule Q M).blocks => p.val (i,x)) he
    have uv : u=v := Subtype.ext (funext fun i => by simpa [f,character_zero] using ev i 0)
    subst v
    refine Prod.ext rfl (Subtype.ext (character_injective (funext fun x => ?_)))
    exact add_left_cancel (show u.val o+character c.val x=u.val o+character b.val x from ev o x)
  · intro u
    obtain ⟨c,h⟩ := restrict_check (fourRule_compatible Q M) star u
    have hom := (check_iff_complete _ _).mp u.prop
    have zero (i j k : I) : fourth M i j k 0 0 0=0 := by simp [fourth,move_zero]
    refine ⟨(⟨fun i => u.val (i,0),(check_iff_complete _ _).mpr fun i j k => ?_⟩,c),
      Subtype.ext (funext fun p => (h p.1 p.2).symm)⟩
    simpa only [fourRule,zero] using hom (i,0) (j,0) (k,0)

theorem split_checks_card (Q : Rule I) (M : Matching I) {o : I} (star : Normalized M o) :
    Nat.card (Checks (fourRule Q M).blocks)=Nat.card (Checks Q.blocks)*Nat.card (Invariant M) := by
  rw [← Nat.card_congr (splitChecks Q M star),Nat.card_prod]

#print axioms splitChecks
#print axioms split_checks_card
end Erdos722.FourPoint
