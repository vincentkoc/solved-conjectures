import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite permutation certificates for the second, third and fourth factorial gaps -/

namespace Erdos478.LowGapAction
open Finset Equiv
local instance (n : ℕ) : Fintype (Perm (Fin n)) := fintypePerm
def pointCount {n : ℕ} (g : Perm (Fin n)) : ℕ :=
  (univ.filter fun x => g x=x).card
abbrev Small := (Perm (Fin 2)) × (Perm (Fin 3))
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 2048
theorem two_generators : ∀ u v : Small, pointCount u.1=0 → pointCount u.2=0 →
    pointCount v.2=1 → ∀ a : Small, ∃ i : Fin 6, ∃ j : Fin 2, u^i.val*v^j.val=a := by
  decide +kernel
def pairedRows (r : Perm (Fin 4)) (k : ℕ) : ℕ :=
  (univ.filter fun p : Perm (Fin 4) => p*r=r*p ∧ pointCount p=k).card

theorem quartic_table : ∀ r : Perm (Fin 4), r*r=1 → pointCount r=0 →
    (pairedRows r 0, pairedRows r 1, pairedRows r 2, pairedRows r 3, pairedRows r 4)=(5,0,2,0,1) := by
  decide +kernel
/-- A transposition inside the paired group and an element carrying its moving
pair onto the other pair generate the entire centralizer. -/
theorem pair_generators : ∀ r s t : Perm (Fin 4),
    r*r=1 → pointCount r=0 → s*r=r*s → t*r=r*t → pointCount s=2 →
    (∃ x, s x≠x ∧ s (t x)=t x) → ∀ h : Perm (Fin 4), h*r=r*h →
    ∃ i j k : Fin 2, s^i.val*(t*s*t⁻¹)^j.val*t^k.val=h := by
  decide +kernel

theorem four_fixed : ∀ g : Perm (Fin 4), pointCount g=4 → g=1 := by decide +kernel

theorem two_fixed_moved : ∀ g : Perm (Fin 4), pointCount g=2 →
    ∃ x y, g x≠x ∧ g y=y := by decide +kernel

#print axioms pointCount
#print axioms Small
#print axioms two_generators
#print axioms pairedRows
#print axioms quartic_table
#print axioms pair_generators
#print axioms four_fixed
#print axioms two_fixed_moved
end Erdos478.LowGapAction
