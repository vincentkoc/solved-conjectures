import Erdos722MarkedTranslationKernel
import Erdos722RigidTransversalSpectrum

/-! # Sparse incidence colours on the binary affine basis -/

namespace Erdos722.FourPoint
open Finset QuadCompletion Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

private theorem basis_room (d : ℕ) (hd : 6≤d) :
    2*(affineBasisMarks d).card+1<Fintype.card (Cube d) := by
  have n := sparse_basis_size hd
  have m := affineBasisMarks_bound d
  simpa [Cube] using (show 2*(affineBasisMarks d).card+1<2^d by omega)

def cubePrivateBlocks (d : ℕ) (hd : 6≤d) : affineBasisMarks d → (cubeRule d).blocks :=
  privateBlocks (cubeRule d) (affineBasisMarks d) (basis_room d hd)

theorem cubePrivateBlocks_injective (d : ℕ) (hd : 6≤d) : Function.Injective (cubePrivateBlocks d hd) :=
  privateBlocks_injective ..

theorem cubePrivateBlocks_incident (d : ℕ) (hd : 6≤d) (q : affineBasisMarks d) :
    q.val∈(cubePrivateBlocks d hd q).val := by
  have inter := privateBlocks_inter (cubeRule d) (affineBasisMarks d) (basis_room d hd) q
  have h : q.val∈(cubePrivateBlocks d hd q).val∩affineBasisMarks d := by rw [cubePrivateBlocks,inter]; simp
  exact (mem_inter.mp h).1

/-- After an arbitrary base relabelling there is a point outside the marks in both coordinates. -/
theorem common_unmarked_point (d : ℕ) (hd : 6≤d) (b : Perm (Cube d)) :
    ∃ o, o∉markedSupport (cubePrivateBlocks d hd) ∧ b o∉markedSupport (cubePrivateBlocks d hd) := by
  let U := markedSupport (cubePrivateBlocks d hd)
  let V := U.map b.symm.toEmbedding
  have room : (U∪V).card<(univ : Finset (Cube d)).card := by
    have cover := card_union_le U V
    have card : V.card=U.card := card_map ..
    have small : U.card≤4*(affineBasisMarks d).card := markedSupport_bound _
    have count := affineBasisMarks_bound d
    have n := sparse_basis_size hd
    simpa [Cube] using (show (U∪V).card<2^d by omega)
  obtain ⟨o,_,hout⟩ := exists_mem_notMem_of_card_lt_card room
  simp only [mem_union,not_or] at hout
  exact ⟨o,hout.1,fun h => hout.2 (mem_map.mpr ⟨b o,h,b.symm_apply_apply o⟩)⟩

def cycleCoefficients (d : ℕ) (hd : 6≤d) : IncidenceColours (cubeRule d) :=
  markedColours (cubePrivateBlocks d hd) fun _ => threeCycle

/-- No nonzero fibre translation preserves the offsets of the cycle-marked family. -/
theorem cycle_gradient_injective (d : ℕ) (hd : 6≤d) :
    Function.Injective (weightedGradient (cubeRule d) (cycleCoefficients d hd)) := by
  obtain ⟨o,out,_⟩ := common_unmarked_point d hd (Equiv.refl _)
  intro t s eq
  apply sub_eq_zero.mp
  apply basis_cycle_kernel (cubePrivateBlocks_injective d hd) (cubePrivateBlocks_incident d hd) out
  change weightedGradient (cubeRule d) (cycleCoefficients d hd) (t-s)=0
  rw [map_sub,eq,sub_self]

#print axioms cubePrivateBlocks
#print axioms cubePrivateBlocks_injective
#print axioms cubePrivateBlocks_incident
#print axioms common_unmarked_point
#print axioms cycleCoefficients
#print axioms cycle_gradient_injective
end
end Erdos722.FourPoint
