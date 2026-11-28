import Erdos722LabelledRankOrbits
import Erdos722AffineClassWeight

/-! # The labelled mass of the full next binary rank -/

namespace Erdos722.QuadSwitch
open Finset
open scoped Classical
noncomputable section

theorem affine_switch_count (d : ℕ) :
    (classFibre d (affineClass d)).card=2^(2^d-(d+1)) := by
  change (univ.filter _).card=_
  rw [affine_class_switches]
  have h := exact_gauge_weight (binaryBase d).val
  rw [binaryBase_checks,Fintype.card_fin] at h
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<2^(d+1))
  rw [h,← pow_add,Nat.sub_add_cancel (by have := Nat.lt_two_pow_self (n:=d); omega)]

theorem rank_fibre_sum (d : ℕ) :
    ∑ C∈nextRankClasses d,(classFibre d C).card=2^(blockNumber (2^d))-2^(2^d-(d+1)) := by
  classical
  have h := card_eq_sum_card_image (fun s : Switches d => classOf (binaryDouble d s)) univ
  change (univ : Finset (Switches d)).card=∑ C∈switchClassImage d,(classFibre d C).card at h
  rw [class_image_split,sum_insert (affine_not_next d),affine_switch_count] at h
  have bc : (binaryBase d).val.card=blockNumber (2^d) := by simpa [blockNumber] using base_block_count (binaryBase d).prop
  have cube : (univ : Finset (Switches d)).card=2^(blockNumber (2^d)) := by simp [Switches,bc]
  rw [cube] at h
  rw [h,Nat.add_sub_cancel_left]

/-- Tonchev's labelled enumeration, expressed as an integer identity without
division by a group order. The large factorial counts unrestricted point labels. -/
theorem labelled_rank_mass (d : ℕ) :
    (nextRankSystems d).card*liftOrder d=
      (2^(blockNumber (2^d))-2^(2^d-(d+1)))*(2^(d+1)).factorial := by
  have total := card_eq_sum_card_image classOf (nextRankSystems d)
  change (nextRankSystems d).card=∑ C∈nextRankClasses d,(rankClassLabels d C).card at total
  rw [total,Finset.sum_mul,← rank_fibre_sum,Finset.sum_mul]
  exact sum_congr rfl fun C hC => label_switch_weight d hC

#print axioms affine_switch_count
#print axioms rank_fibre_sum
#print axioms labelled_rank_mass
end
end Erdos722.QuadSwitch
