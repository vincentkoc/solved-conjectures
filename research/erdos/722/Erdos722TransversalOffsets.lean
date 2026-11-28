import Erdos722CompletionParity
import Erdos722FourFibreChecks

/-! # Independent additive offsets on the transversal blocks of a four-point filling -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

abbrev BlockOffsets (Q : Rule I) := Q.blocks → Fibre

def offsetAt (Q : Rule I) (u : BlockOffsets Q) (S : Finset I) : Fibre :=
  if h : S∈Q.blocks then u ⟨S,h⟩ else 0

def transversalOffset (Q : Rule I) (u : BlockOffsets Q) (i j k : I) : Fibre :=
  offsetAt Q u (insert (Q.complete i j k) {i,j,k})

theorem offset_on_block (Q : Rule I) (u : BlockOffsets Q) {i j k : I}
    (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    transversalOffset Q u i j k = u ⟨_,completed_block Q ij ik jk⟩ :=
  dif_pos (completed_block Q ij ik jk)

theorem offset_swap₁ (Q : Rule I) (u : BlockOffsets Q) (i j k : I) :
    transversalOffset Q u i j k=transversalOffset Q u j i k := by
  unfold transversalOffset
  rw [Q.swap₁ i j k,insert_comm i j]

theorem offset_swap₂ (Q : Rule I) (u : BlockOffsets Q) (i j k : I) :
    transversalOffset Q u i j k=transversalOffset Q u i k j := by
  unfold transversalOffset
  rw [Q.swap₂ i j k]
  congr 2
  ext x
  simp [or_comm]

theorem offset_cancel (Q : Rule I) (u : BlockOffsets Q) (i j k : I) :
    transversalOffset Q u i j (Q.complete i j k)=transversalOffset Q u i j k := by
  unfold transversalOffset
  rw [Q.cancel]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem offset_repeated (Q : Rule I) (u : BlockOffsets Q) (i j : I) : transversalOffset Q u i i j=0 := by
  unfold transversalOffset
  rw [Q.repeated]
  apply dif_neg
  intro h
  have size := ((Q.mem_blocks _).mp h).1
  by_cases eq : i=j
  · subst j; simp at size
  · simp [eq,insert_comm j i] at size

/-- On a distinct triple each direction of offset can be read back from its block. -/
theorem offset_injective (Q : Rule I) : Function.Injective (transversalOffset Q) := by
  intro u v he
  funext B
  obtain ⟨hc,closed⟩ := (Q.mem_blocks _).mp B.prop
  obtain ⟨a,b,c,z,ab,ac,az,bc,bz,cz,eq⟩ := card_eq_four.mp hc
  have sub : ({a,b,c}:Finset I)⊆B.val := by rw [eq]; simp
  have mem := closed a (sub (by simp)) b (sub (by simp)) c (sub (by simp))
  have fr := Q.fresh ab ac bc
  rw [eq] at mem
  simp only [mem_insert,mem_singleton,not_or] at mem fr
  have f : Q.complete a b c=z := by tauto
  have same : (⟨_,completed_block Q ab ac bc⟩ : Q.blocks)=B := by
    apply Subtype.ext
    change insert (Q.complete a b c) {a,b,c}=B.val
    rw [eq,f]
    ext x
    simp only [mem_insert,mem_singleton]
    tauto
  have h := congrFun (congrFun (congrFun he a) b) c
  rwa [offset_on_block Q u ab ac bc,offset_on_block Q v ab ac bc,same] at h

#print axioms BlockOffsets
#print axioms offsetAt
#print axioms transversalOffset
#print axioms offset_on_block
#print axioms offset_swap₁
#print axioms offset_swap₂
#print axioms offset_cancel
#print axioms offset_repeated
#print axioms offset_injective
end
end Erdos722.FourPoint
