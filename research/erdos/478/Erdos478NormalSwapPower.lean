import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign

/-! # Relative symmetric-group actions detected by a power of one element -/

namespace Erdos478.TetrahedralGap
open Equiv Function

/-- If a power fixes all lower data and acts by a transposition on a full
symmetric quotient, that quotient remains full over the lower kernel.
The degree can be composite. -/
theorem relative_swap_power {G H X : Type*} [Group G] [Group H] [Fintype X] [DecidableEq X]
    (lower : G →* H) (act : G →* Perm X) (onto : Surjective act) (g : G) (n : ℕ)
    (kill : lower (g^n)=1) (swap : (act (g^n)).IsSwap) :
    Surjective (act.comp lower.ker.subtype) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Perm.closure_isSwap]
  refine (Subgroup.closure_le _).2 ?_
  intro u hu
  have conj : IsConj (act (g^n)) u := Perm.isConj_iff_cycleType_eq.mpr
    ((Perm.isSwap_iff_cycleType.mp swap).trans (Perm.isSwap_iff_cycleType.mp hu).symm)
  obtain ⟨π,hπ⟩ := isConj_iff.mp conj
  obtain ⟨k,hk⟩ := onto π
  refine ⟨⟨k*g^n*k⁻¹,?_⟩,?_⟩
  · change lower (k*g^n*k⁻¹)=1
    rw [map_mul,map_mul,map_inv,kill,mul_one,mul_inv_cancel]
  · change act (k*g^n*k⁻¹)=u
    rw [map_mul,map_mul,map_inv,hk]
    exact hπ

#print axioms relative_swap_power
end Erdos478.TetrahedralGap
