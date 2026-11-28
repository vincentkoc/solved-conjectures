import Erdos722QuadCompletion
import Erdos722BinaryIncidenceRank

/-! # Testing binary checks on the ternary completion of a quadruple system -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A distinct triple and its fourth point give the unique host block through the triple. -/
theorem completed_block (Q : Rule V) {a b c : V} (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    insert (Q.complete a b c) {a,b,c} ∈ Q.blocks := by
  have ht : ({a,b,c} : Finset V).card=3 := card_eq_three.mpr ⟨a,b,c,ab,ac,bc,rfl⟩
  obtain ⟨B,⟨hb,sub⟩,_⟩ := Q.isBlockDesign.2 _ ht
  obtain ⟨size,closed⟩ := (Q.mem_blocks _).mp hb
  have eq : insert (Q.complete a b c) {a,b,c}=B := by
    apply eq_of_subset_of_card_le
    · exact insert_subset (closed a (sub (by simp)) b (sub (by simp)) c (sub (by simp))) sub
    · rw [card_insert_of_notMem (Q.fresh ab ac bc),size,ht]
  rwa [eq]

theorem check_iff_complete (Q : Rule V) (f : V → ZMod 2) :
    Check Q.blocks f ↔ ∀ a b c, f (Q.complete a b c)=f a+f b+f c := by
  have rel : ∀ a b c z : ZMod 2, z+(a+(b+c))=0 ↔ z=a+b+c := by decide
  constructor
  · intro h a b c
    by_cases ab : a=b
    · subst b; simp [Q.repeated,CharTwo.add_self_eq_zero]
    by_cases ac : a=c
    · subst c; rw [Q.swap₂,Q.repeated]; exact
        (show ∀ x y : ZMod 2, y=x+y+x by decide) _ _
    by_cases bc : b=c
    · subst c; rw [Q.swap₁,Q.swap₂,Q.repeated,add_assoc,CharTwo.add_self_eq_zero,add_zero]
    apply (rel ..).mp
    simpa [blockSum,Q.fresh ab ac bc,ab,ac,bc] using h _ (completed_block Q ab ac bc)
  · intro h B hb
    obtain ⟨hc,closed⟩ := (Q.mem_blocks _).mp hb
    obtain ⟨a,b,c,z,ab,ac,az,bc,bz,cz,rfl⟩ := card_eq_four.mp hc
    have mem := closed a (by simp) b (by simp) c (by simp)
    have fresh := Q.fresh ab ac bc
    simp only [mem_insert,mem_singleton,not_or] at mem fresh
    have he : Q.complete a b c=z := by tauto
    have eq := h a b c
    rw [he] at eq
    simp [blockSum,ab,ac,az,bc,bz,cz,eq,add_comm,add_left_comm,CharTwo.add_self_eq_zero]

#print axioms completed_block
#print axioms check_iff_complete
end Erdos722.FourPoint
