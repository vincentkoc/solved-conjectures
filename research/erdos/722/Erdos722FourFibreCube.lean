import Erdos722CompletionParity
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The parity checks of the affine quadruple system on binary coordinates -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch Module
abbrev Cube (d : ℕ) := Fin d → ZMod 2

def cubeRule (d : ℕ) : Rule (Cube d) where
  complete x y z := x+y+z
  swap₁ x y z := by rw [add_comm x y]
  swap₂ x y z := by ac_rfl
  repeated x y := by funext i; exact (show ∀ a b : ZMod 2, a+a+b=b by decide) _ _
  cancel x y z := by funext i; exact (show ∀ a b c : ZMod 2, a+b+(a+b+c)=c by decide) _ _ _

/-- The usual linear part and constant term, including the zero-dimensional base. -/
noncomputable def cubeChecks (d : ℕ) [DecidableEq (Cube d)] :
    Module.Dual (ZMod 2) (Cube d) × ZMod 2 ≃ Checks (cubeRule d).blocks := by
  let f (p : Module.Dual (ZMod 2) (Cube d) × ZMod 2) : Checks (cubeRule d).blocks :=
    ⟨fun x => p.1 x+p.2,(check_iff_complete _ _).mpr fun a b c => by
      change p.1 (a+b+c)+p.2=_
      simp only [map_add]
      exact (show ∀ a b c w : ZMod 2, a+b+c+w=a+w+(b+w)+(c+w) by decide) _ _ _ _⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨L,c⟩ ⟨M,b⟩ he
    have ev (x : Cube d) := congrArg (fun v : Checks (cubeRule d).blocks => v.val x) he
    have cb : c=b := by simpa [f] using ev 0
    subst b
    exact Prod.ext (LinearMap.ext fun x => add_right_cancel (show L x+c=M x+c from ev x)) rfl
  · intro u
    have h := (check_iff_complete _ _).mp u.prop
    let l : Cube d →+ ZMod 2 :=
      { toFun := fun x => u.val x+u.val 0
        map_zero' := CharTwo.add_self_eq_zero _
        map_add' := fun x y => by
          have eq : u.val (x+y)=u.val x+u.val y+u.val 0 := by
            simpa [cubeRule] using h x y 0
          rw [eq]
          exact (show ∀ a b c : ZMod 2, a+b+c+c=a+c+(b+c) by decide) _ _ _ }
    refine ⟨(l.toZModLinearMap 2,u.val 0),Subtype.ext (funext fun x => ?_)⟩
    exact (show ∀ a b : ZMod 2, a+b+b=a by decide) _ _

theorem cube_checks_card (d : ℕ) [DecidableEq (Cube d)] : Nat.card (Checks (cubeRule d).blocks)=2^(d+1) := by
  rw [← Nat.card_congr (cubeChecks d),Nat.card_prod,
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Module.Dual (ZMod 2) (Cube d)),
    Subspace.dual_finrank_eq,pow_succ]
  simp [Cube,Nat.card_eq_fintype_card]

#print axioms Cube
#print axioms cubeRule
#print axioms cubeChecks
#print axioms cube_checks_card
end Erdos722.FourPoint
