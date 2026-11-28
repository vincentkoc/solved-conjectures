import Erdos722SplitFourFibreIsomorphisms
import Mathlib.GroupTheory.SemidirectProduct

/-! # The colour stabilizer and the additive group of translations -/

namespace Erdos722.FourPoint
open Equiv QuadCompletion QuadSwitch
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Base automorphisms and colours that together preserve every matching. -/
def baseFrames (Q : Rule I) (M : Matching I) : Subgroup (Perm I × Colour) where
  carrier := {g | (∀ i j k, g.1 (Q.complete i j k)=Q.complete (g.1 i) (g.1 j) (g.1 k)) ∧ Frame M M g.1 g.2}
  one_mem' := ⟨fun _ _ _ => rfl,fun _ _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha,fa⟩ ⟨hb,fb⟩
    constructor
    · intro i j k
      change a.1 (b.1 (Q.complete i j k))=Q.complete (a.1 (b.1 i)) (a.1 (b.1 j)) (a.1 (b.1 k))
      rw [hb,ha]
    · intro i j
      change (a.2*b.2)*M.transport i j=M.transport (a.1 (b.1 i)) (a.1 (b.1 j))*(a.2*b.2)
      rw [mul_assoc,fb,← mul_assoc,fa,mul_assoc]
  inv_mem' := by
    rintro g ⟨hg,fg⟩
    constructor
    · intro i j k
      apply g.1.injective
      change g.1 (g.1.symm (Q.complete i j k))=g.1 (Q.complete (g.1.symm i) (g.1.symm j) (g.1.symm k))
      rw [hg]; simp only [Equiv.apply_symm_apply]
    · intro i j
      change g.2⁻¹*M.transport i j=M.transport (g.1.symm i) (g.1.symm j)*g.2⁻¹
      have f := fg (g.1.symm i) (g.1.symm j)
      simp only [Equiv.apply_symm_apply] at f
      calc
        _ = g.2⁻¹*(M.transport i j*g.2)*g.2⁻¹ := by group
        _ = _ := by rw [← f]; group

/-- The fibre translations form the two-coordinate binary check group. -/
def shifts (Q : Rule I) : AddSubgroup (I → Fibre) where
  carrier := {t | Offset Q t}
  zero_mem' := fun _ _ _ => by simp
  add_mem' := by
    intro a b ha hb i j k
    change a (Q.complete i j k)+b (Q.complete i j k)=a i+b i+(a j+b j)+(a k+b k)
    rw [ha i j k,hb i j k]; ac_rfl
  neg_mem' := by
    intro a ha i j k
    change -(a (Q.complete i j k))= -a i+-a j+-a k
    rw [ha i j k]; abel

def shiftsEquivChecks (Q : Rule I) : shifts Q ≃ Checks Q.blocks × Checks Q.blocks where
  toFun t := (⟨fun i => (t.val i).1,(check_iff_complete ..).mpr fun i j k => congrArg Prod.fst (t.prop i j k)⟩,
    ⟨fun i => (t.val i).2,(check_iff_complete ..).mpr fun i j k => congrArg Prod.snd (t.prop i j k)⟩)
  invFun f := ⟨fun i => (f.1.val i,f.2.val i),fun i j k => Prod.ext
    ((check_iff_complete ..).mp f.1.prop i j k) ((check_iff_complete ..).mp f.2.prop i j k)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem shifts_card (Q : Rule I) : Nat.card (shifts Q)=Nat.card (Checks Q.blocks)^2 := by
  rw [← Nat.card_congr (shiftsEquivChecks Q).symm,Nat.card_prod,pow_two]

#print axioms baseFrames
#print axioms shifts
#print axioms shiftsEquivChecks
#print axioms shifts_card
end Erdos722.FourPoint
