import Erdos722BinaryCheckBases
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! # The binary incidence rank and the number of parity checks -/

namespace Erdos722.QuadSwitch
open Finset Matrix Module
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V))

def binaryIncidence : Matrix H V (ZMod 2) := fun B x => if x∈B.val then 1 else 0

theorem incidence_mul (f : V → ZMod 2) (B : H) :
    (binaryIncidence H).mulVec f B=blockSum f B.val := by
  classical
  change (∑ x, (if x∈B.val then (1:ZMod 2) else 0)*f x)=_
  simp only [ite_mul,one_mul,zero_mul,← Finset.sum_filter]
  simp [blockSum]

def checksKernel : Checks H ≃ LinearMap.ker (binaryIncidence H).mulVecLin :=
  Equiv.subtypeEquivRight fun f => by
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      funext B
      change (binaryIncidence H).mulVec f B=0
      rw [incidence_mul]
      exact h B.val B.prop
    · intro he B hB
      have h := congrFun he ⟨B,hB⟩
      change (binaryIncidence H).mulVec f ⟨B,hB⟩=0 at h
      rwa [incidence_mul] at h

/-- Rank is the ordinary matrix rank of the binary block-by-point incidence matrix. -/
theorem checks_card_rank : Nat.card (Checks H)=2^(Fintype.card V-(binaryIncidence H).rank) := by
  rw [Nat.card_congr (checksKernel H),Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_eq_fintype_card,ZMod.card]
  have dims := (binaryIncidence H).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at dims
  change (binaryIncidence H).rank+_=Fintype.card V at dims
  congr 1
  omega

#print axioms binaryIncidence
#print axioms incidence_mul
#print axioms checksKernel
#print axioms checks_card_rank
end
end Erdos722.QuadSwitch
