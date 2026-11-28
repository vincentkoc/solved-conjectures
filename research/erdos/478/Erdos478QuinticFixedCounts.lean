import Erdos478PermutationCountLaw

/-! # The fixed-point distribution of the symmetric group on the five quintic roots -/

namespace Erdos478.QuinticLaw
open Finset Equiv LowGapAction FrobeniusCounts
local instance : Fintype (Perm (Fin 5)) := fintypePerm

def quinticWeight (m : Fin 6 → Bool) : ℕ :=
  44*(m 0).toNat+45*(m 1).toNat+20*(m 2).toNat+10*(m 3).toNat+(m 5).toNat

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 2048 in
private theorem quintic_table : ∀ m : Fin 6 → Bool,
    (univ.filter fun p : Perm (Fin 5) => m (countIndex p)=true).card=quinticWeight m := by
  decide +kernel

noncomputable section
theorem quintic_mean (m : ℕ → Bool) :
    uniform (Perm (Fin 5)) (fun p => if m (pointCount p) then 1 else 0)=
      ((quinticWeight (fun i => m i.val) : ℕ) : ℝ)/120 := by
  have count := quintic_table (fun i => m i.val)
  have size : Fintype.card (Perm (Fin 5))=120 := by decide +kernel
  simp only [uniform,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_boole,size,Nat.cast_ofNat]
  rw [← count]
  rfl

#print axioms quinticWeight
#print axioms quintic_mean
end
end Erdos478.QuinticLaw
