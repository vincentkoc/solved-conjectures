import Erdos722FourFibreRecovery

/-! # Block isomorphisms and ternary completion isomorphisms -/

namespace Erdos722.FourPoint
open QuadCompletion Finset
variable {A B : Type*} [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]

/-- An invertible map preserving ternary completion carries the entire block set. -/
theorem blocks_of_completion (Q : Rule A) (R : Rule B) (e : A ≃ B)
    (h : ∀ a b c, e (Q.complete a b c)=R.complete (e a) (e b) (e c)) :
    e.finsetCongr.finsetCongr Q.blocks=R.blocks := by
  apply Subset.antisymm
  · intro T hT
    obtain ⟨U,hU,rfl⟩ := mem_map.mp hT
    exact Q.map_block R e.toEmbedding h hU
  · have rev (a b c : B) : e.symm (R.complete a b c)=Q.complete (e.symm a) (e.symm b) (e.symm c) := by
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using (h (e.symm a) (e.symm b) (e.symm c)).symm
    intro T hT
    exact mem_map.mpr ⟨e.symm.finsetCongr T,R.map_block Q e.symm.toEmbedding rev hT,
      e.finsetCongr.apply_symm_apply T⟩

/-- The unique block through each distinct triple recovers its completion.
The repeated-point identities handle the remaining triples. -/
theorem completion_of_blocks (Q : Rule A) (R : Rule B) (e : A ≃ B)
    (h : e.finsetCongr.finsetCongr Q.blocks=R.blocks) (a b c : A) :
    e (Q.complete a b c)=R.complete (e a) (e b) (e c) := by
  let T : Rule A := {
    complete := fun x y z => e.symm (R.complete (e x) (e y) (e z))
    swap₁ := fun x y z => congrArg e.symm (R.swap₁ ..)
    swap₂ := fun x y z => congrArg e.symm (R.swap₂ ..)
    repeated := fun x y => by simp [R.repeated]
    cancel := fun x y z => by simp [R.cancel] }
  have ht : e.finsetCongr.finsetCongr T.blocks=R.blocks := blocks_of_completion T R e
    (fun x y z => e.apply_symm_apply _)
  have eq := completion_determined Q T (e.finsetCongr.finsetCongr.injective (h.trans ht.symm)) a b c
  exact (congrArg e eq).trans (e.apply_symm_apply _)

#print axioms blocks_of_completion
#print axioms completion_of_blocks
end Erdos722.FourPoint
