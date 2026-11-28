import Erdos478LowJointSurjection
import Erdos478UniformQuotientLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # The exact product law for three low-degree fixed-point counts -/

namespace Erdos478.LowGapAction
open Finset Equiv FrobeniusCounts
local instance (n : ℕ) : Fintype (Perm (Fin n)) := fintypePerm

def countIndex {k : ℕ} (p : Perm (Fin k)) : Fin (k+1) :=
  ⟨pointCount p, Nat.lt_succ_of_le ((card_filter_le ..).trans_eq (by simp))⟩

def binaryWeight (m : Fin 3 → Bool) : ℕ := (m 0).toNat+(m 2).toNat
def cubicWeight (m : Fin 4 → Bool) : ℕ := 2*(m 0).toNat+3*(m 1).toNat+(m 3).toNat
def quarticWeight (m : Fin 5 → Bool) : ℕ := 5*(m 0).toNat+2*(m 2).toNat+(m 4).toNat

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 2048

private theorem binary_count : ∀ m : Fin 3 → Bool,
    (univ.filter fun p : Perm (Fin 2) => m (countIndex p)=true).card=binaryWeight m := by decide +kernel
private theorem cubic_count : ∀ m : Fin 4 → Bool,
    (univ.filter fun p : Perm (Fin 3) => m (countIndex p)=true).card=cubicWeight m := by decide +kernel
private theorem quartic_count : ∀ r : Perm (Fin 4), r*r=1 → pointCount r=0 → ∀ m : Fin 5 → Bool,
    (univ.filter fun p : Perm (Fin 4) => p*r=r*p ∧ m (countIndex p)=true).card=quarticWeight m := by
  decide +kernel

noncomputable section
open scoped Classical
private theorem paired_count (r : Perm (Fin 4)) (inv : r*r=1) (free : pointCount r=0)
    (m : Fin 5 → Bool) :
    (univ.filter fun p : PairGroup r => m (countIndex p.val)=true).card=quarticWeight m := by
  classical
  let P (p : Perm (Fin 4)) := p∈PairGroup r
  let Q (p : Perm (Fin 4)) := m (countIndex p)=true
  have h := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter P Q)
  rw [Fintype.card_subtype,Fintype.card_subtype] at h
  calc
    _ = (univ.filter fun p => P p ∧ Q p).card := h
    _ = _ := by simpa only [P,Q,Subgroup.mem_centralizer_singleton_iff] using quartic_count r inv free m

/-- Each Boolean mask selects any set of endpoint counts. The margins have
weights (1,0,1), (2,3,0,1), and (5,0,2,0,1), respectively. -/
theorem model_probability (r : Perm (Fin 4)) (inv : r*r=1) (free : pointCount r=0)
    (a : Fin 3 → Bool) (b : Fin 4 → Bool) (c : Fin 5 → Bool) :
    uniform (Small × PairGroup r) (fun q => if a (countIndex q.1.1) && b (countIndex q.1.2) &&
      c (countIndex q.2.val) then 1 else 0) = ((binaryWeight a*cubicWeight b*quarticWeight c : ℕ):ℝ)/96 := by
  classical
  let A (p : Perm (Fin 2)) := a (countIndex p)=true
  let B (p : Perm (Fin 3)) := b (countIndex p)=true
  let C (p : PairGroup r) := c (countIndex p.val)=true
  have pc := paired_count r inv free (fun _ => true)
  simp only [filter_true,card_univ] at pc
  have size : Fintype.card (Small × PairGroup r)=96 := by
    rw [Fintype.card_prod,pc,show quarticWeight (fun _ => true)=8 by decide]
    decide +kernel
  have cnt : (univ.filter fun q : Small × PairGroup r => (A q.1.1 ∧ B q.1.2) ∧ C q.2).card=
      binaryWeight a*cubicWeight b*quarticWeight c := by
    rw [← univ_product_univ,filter_product (fun z : Small => A z.1 ∧ B z.2) C,card_product,
      ← univ_product_univ,filter_product A B,card_product]
    exact congrArg₂ (·*·) (congrArg₂ (·*·) (binary_count a) (cubic_count b)) (paired_count r inv free c)
  simp only [uniform,LinearMap.coe_mk,AddHom.coe_mk,Bool.and_eq_true,Finset.sum_boole,size,
    Nat.cast_ofNat,← cnt,A,B,C]

#print axioms countIndex
#print axioms binaryWeight
#print axioms cubicWeight
#print axioms quarticWeight
#print axioms model_probability
end
end Erdos478.LowGapAction
