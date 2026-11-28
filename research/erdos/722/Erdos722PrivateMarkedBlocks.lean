import Erdos722BlockwiseFibreCoordinates

/-! # Base quadruples with a prescribed unique marked point -/

namespace Erdos722.FourPoint
open QuadCompletion Finset
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

omit [DecidableEq I] in
private theorem outside_set (A : Finset I) (small : A.card<Fintype.card I) : ∃ x, x∉A := by
  obtain ⟨x,_,h⟩ := exists_mem_notMem_of_card_lt_card (s:=A) (t:=univ) (by simpa using small)
  exact ⟨x,h⟩

/-- Through each marked point choose a quadruple meeting the marked set only there.
For fixed first and second points, completion is an involution, so at most
twice the number of marks plus one third points are forbidden. -/
theorem private_block_exists (Q : Rule I) (A : Finset I) (size : 2*A.card+1<Fintype.card I)
    (q : A) : ∃ B : Q.blocks, B.val ∩ A={q.val} := by
  obtain ⟨j,hj⟩ := outside_set A (by omega)
  let bad := insert j (A∪A.image (Q.complete q.val j))
  have small : bad.card<Fintype.card I := by
    have h₁ := card_insert_le j (A∪A.image (Q.complete q.val j))
    have h₂ := card_union_le A (A.image (Q.complete q.val j))
    have h₃ := card_image_le (s:=A) (f:=Q.complete q.val j)
    dsimp only [bad]
    omega
  obtain ⟨k,hk⟩ := outside_set bad small
  simp only [bad,mem_insert,mem_union,not_or] at hk
  have hl : Q.complete q.val j k∉A := by
    intro inside
    exact hk.2.2 (mem_image.mpr ⟨_,inside,Q.cancel ..⟩)
  have qj : q.val≠j := fun eq => hj (eq ▸ q.prop)
  have qk : q.val≠k := fun eq => hk.2.1 (eq ▸ q.prop)
  refine ⟨⟨_,completed_block Q qj qk (Ne.symm hk.1)⟩,?_⟩
  ext x
  simp only [mem_inter,mem_insert,mem_singleton]
  constructor
  · rintro ⟨rfl|rfl|rfl|rfl,h⟩
    · exact (hl h).elim
    · rfl
    · exact (hj h).elim
    · exact (hk.2.1 h).elim
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl),q.prop⟩

def privateBlocks (Q : Rule I) (A : Finset I) (size : 2*A.card+1<Fintype.card I) (q : A) : Q.blocks :=
  (private_block_exists Q A size q).choose

theorem privateBlocks_inter (Q : Rule I) (A : Finset I) (size : 2*A.card+1<Fintype.card I) (q : A) :
    (privateBlocks Q A size q).val ∩ A={q.val} := (private_block_exists Q A size q).choose_spec

theorem privateBlocks_injective (Q : Rule I) (A : Finset I) (size : 2*A.card+1<Fintype.card I) :
    Function.Injective (privateBlocks Q A size) := by
  intro q r eq
  have h := privateBlocks_inter Q A size q
  rw [eq,privateBlocks_inter] at h
  exact Subtype.ext (Finset.singleton_injective h.symm)

def markedSupport {A : Finset I} {Q : Rule I} (m : A → Q.blocks) : Finset I :=
  univ.biUnion fun q => (m q).val

theorem markedSupport_bound {A : Finset I} {Q : Rule I} (m : A → Q.blocks) :
    (markedSupport m).card≤4*A.card := by
  calc
    _ ≤ ∑ q : A, (m q).val.card := card_biUnion_le
    _ = 4*A.card := by
      have card (q : A) : (m q).val.card=4 := ((Q.mem_blocks _).mp (m q).prop).1
      simp [card,Nat.mul_comm]

#print axioms private_block_exists
#print axioms privateBlocks
#print axioms privateBlocks_inter
#print axioms privateBlocks_injective
#print axioms markedSupport
#print axioms markedSupport_bound
end
end Erdos722.FourPoint
