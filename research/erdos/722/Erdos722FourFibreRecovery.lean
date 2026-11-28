import Erdos722FourFibreEdges

/-! # Recovery of each direction matching from the labelled blocks -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem completion_determined (Q R : Rule V) (same : Q.blocks=R.blocks) (a b c : V) :
    Q.complete a b c=R.complete a b c := by
  by_cases ab : a=b
  · subst b; rw [Q.repeated,R.repeated]
  by_cases ac : a=c
  · subst c; rw [Q.swap₂,R.swap₂,Q.repeated,R.repeated]
  by_cases bc : b=c
  · subst c; rw [Q.swap₁,R.swap₁,Q.swap₂,R.swap₂,Q.repeated,R.repeated]
  have hb := completed_block Q ab ac bc
  rw [same] at hb
  have inside := ((R.mem_blocks _).mp hb).2 a (by simp) b (by simp) c (by simp)
  have fresh := R.fresh ab ac bc
  simp only [mem_insert,mem_singleton,not_or] at inside fresh
  tauto

variable {I : Type*} [LinearOrder I] [Fintype I]

theorem edge_blocks_injective (Q : Rule I) (o : I) :
    Function.Injective (fun w : edges o → Colour => (fourRule Q (edgeMatching o w)).blocks) := by
  intro w v eq
  funext e
  apply Equiv.ext
  intro d
  let i := e.val.1
  let j := e.val.2
  have h := congrArg Prod.snd (completion_determined _ _ eq (i,0) (i,vector d) (j,0))
  change fourth (edgeMatching o w) i i j 0 (vector d) 0=fourth (edgeMatching o v) i i j 0 (vector d) 0 at h
  simp only [fourth,ite_true,zero_add,i,j,edge_forward,move_vector] at h
  simpa only [direction_vector] using congrArg direction h

#print axioms completion_determined
#print axioms edge_blocks_injective
end Erdos722.FourPoint
