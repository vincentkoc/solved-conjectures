import Erdos722RankOrbitWeights

/-! # Excess orbit mass bounds the number of exceptional unrestricted classes -/

namespace Erdos722.QuadSwitch
open Finset Equiv
open scoped Classical
noncomputable section

def liftOrder (d : ℕ) := Nat.card (automorphisms (binaryBase d).val)*2^(2^d)

theorem binary_lift_card (d : ℕ) : Nat.card (liftGroup (binaryBase d).val)=liftOrder d := by
  rw [← Nat.card_congr (liftCoordinates _),Nat.card_prod]
  simp [liftOrder,Nat.card_eq_fintype_card]

/-- All orbits carry at least one copy of the vertical check group in their
stabilizer. An exceptional next-rank orbit carries at least two. -/
theorem exceptional_orbit_defect (d : ℕ) :
    (exceptionalRankClasses d).card*liftOrder d + 2*(2^(d+1)*2^(blockNumber (2^d))) ≤
      2*((nextRankClasses d).card+1)*liftOrder d := by
  classical
  let M := switchClassImage d
  let B := exceptionalRankClasses d
  let g := liftOrder d
  let c := 2^(d+1)
  let r (C : DesignClass (RankPoints d)) := (classFibre d C).card
  have bc : (binaryBase d).val.card=blockNumber (2^d) := by
    simpa [blockNumber] using base_block_count (binaryBase d).prop
  have total : ∑ C∈M,r C=2^blockNumber (2^d) := by
    have h := card_eq_sum_card_image (fun s : Switches d => classOf (binaryDouble d s)) univ
    change _=∑ C∈M,r C at h
    rw [← h]
    simp [Switches,bc]
  have handles (C : DesignClass (RankPoints d)) (hC : C∈M) :
      (if C∈B then g else 0)+2*c*r C≤2*g := by
    obtain ⟨s,_,rfl⟩ := mem_image.mp hC
    let C := classOf (binaryDouble d s)
    let a := Nat.card (SwitchStabilizer (binaryBase d).prop s)
    have orbit : r C*a=g := (class_fibre_stabilizer d s).trans (binary_lift_card d)
    have lower : c≤a := by
      have dvd := checks_dvd_stabilizer (binaryBase d).prop s
      rw [binaryBase_checks] at dvd
      exact Nat.le_of_dvd Nat.card_pos dvd
    by_cases bad : C∈B
    · have twice : 2*c≤a := bad_stabilizer_twice d s bad
      change (if C∈B then g else 0)+2*c*r C≤2*g
      rw [if_pos bad]
      nlinarith [Nat.mul_le_mul_left (r C) twice]
    · change (if C∈B then g else 0)+2*c*r C≤2*g
      rw [if_neg bad,zero_add]
      nlinarith [Nat.mul_le_mul_left (r C) lower]
  have small : B⊆M := by
    intro C h
    rw [show M=insert (affineClass d) (nextRankClasses d) from class_image_split d]
    exact mem_insert_of_mem (mem_filter.mp h).1
  have filt : M.filter (·∈B)=B := by ext C; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => small h)
  have indicator : (∑ C∈M,if C∈B then g else 0)=B.card*g := by
    rw [← sum_filter,filt,sum_const,nsmul_eq_mul,Nat.cast_id]
  have q := sum_le_sum handles
  rw [sum_add_distrib,indicator,← Finset.mul_sum,total,sum_const,nsmul_eq_mul] at q
  have classes : M.card=(nextRankClasses d).card+1 := by
    rw [show M=insert (affineClass d) (nextRankClasses d) from class_image_split d,card_insert_of_notMem (affine_not_next d)]
  rw [classes] at q
  change B.card*g+2*(c*2^blockNumber (2^d))≤2*((nextRankClasses d).card+1)*g
  nlinarith only [q]

#print axioms liftOrder
#print axioms binary_lift_card
#print axioms exceptional_orbit_defect
end
end Erdos722.QuadSwitch
