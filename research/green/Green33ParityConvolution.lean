import Green33TailEnergy
import Mathlib.Combinatorics.Additive.Convolution
/-! Counting convolution in the two parity classes of a critical cyclic basis. -/
open Finset AddMonoidAlgebra
open scoped BigOperators
namespace Green33ParityConvolution
variable {G:Type*} [AddCommGroup G] [Fintype G]
abbrev Measures (G:Type*) [AddCommGroup G] := AddMonoidAlgebra ℝ G
noncomputable def weights (f:G→ℝ) : Measures G := ofCoeff (Finsupp.equivFunOnFinite.symm f)
noncomputable def ones : Measures G := weights fun _ => 1
noncomputable def mass (x:Measures G):ℝ:=∑ g,x.coeff g
noncomputable def totalVariation (x:Measures G):ℝ:=∑ g,|x.coeff g|

theorem coeff_weights (f:G→ℝ) (g:G) : (weights f).coeff g=f g := by rfl
theorem coeff_product (x y:Measures G) (g:G) :
    (x*y).coeff g=∑ i,x.coeff i*y.coeff (g-i) := by
  rw [coeff_mul_apply_left,Finsupp.sum_fintype _ _ (by simp)]
  simp only [sub_eq_add_neg,add_comm g]

theorem variation_product (x y:Measures G) :
    totalVariation (x*y)≤totalVariation x*totalVariation y := by
  simp only [totalVariation,coeff_product]
  calc
    _ ≤ ∑ g,∑ i,|x.coeff i| *|y.coeff (g-i)| := by
      apply sum_le_sum
      intro g _
      simpa only [abs_mul] using abs_sum_le_sum_abs (fun i => x.coeff i*y.coeff (g-i)) univ
    _ = _ := by
      rw [sum_comm,sum_mul]
      apply sum_congr rfl
      intro i _
      rw [←mul_sum]
      congr 1
      exact Equiv.sum_comp (Equiv.subRight i) fun z => |y.coeff z|
#print axioms variation_product

private theorem mul_ones (x:Measures G) : x*ones=mass x • ones := by
  apply AddMonoidAlgebra.ext
  ext g
  simp only [coeff_product,ones,coeff_weights,mul_one,coeff_smul_apply,smul_eq_mul,mass]

theorem mass_product (x y:Measures G) : mass (x*y)=mass x*mass y := by
  simp only [mass,coeff_product]
  rw [sum_comm,sum_mul]
  apply sum_congr rfl
  intro i _
  rw [←mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight i) fun z => y.coeff z

private theorem dirac_ones (z:G) : single z (1:ℝ)*ones=ones := by
  apply AddMonoidAlgebra.ext
  ext g
  rw [coeff_single_mul_apply,one_mul]
  rfl

/-- The fourth power of the even layer is determined in the group algebra by
the two observable full-basis errors. The odd-odd sums carry the shift z. -/
theorem fourth_identity (A B:Measures G) (z:G) :
    A^4-(2*mass (A^2)-Fintype.card G) • ones =
      (A^2+single z 1*B^2-(2:ℝ) • ones)*A^2 -
      single z 1*((A*B-ones)*(A*B+ones)) := by
  have jj:(ones:Measures G)*ones=(Fintype.card G:ℝ) • ones := by
    rw [mul_ones];congr 1;simp [mass,ones,coeff_weights]
  have a:ones*A^2=mass (A^2) • ones := by rw [mul_comm,mul_ones]
  have q:(A*B-ones)*(A*B+ones)=(A*B)^2-ones*ones := by ring
  rw [q,jj,mul_sub,mul_smul_comm,dirac_ones,sub_mul,smul_mul_assoc,a,smul_smul,sub_smul]
  ring
#print axioms fourth_identity

private theorem variation_sub (x y:Measures G) :
    totalVariation (x-y)≤totalVariation x+totalVariation y := by
  simp only [totalVariation,coeff_sub,Finsupp.sub_apply,←sum_add_distrib]
  exact sum_le_sum fun g _ => abs_sub _ _

private theorem shift_variation (h:G) (x:Measures G) :
    totalVariation (single h 1*x)=totalVariation x := by
  simp only [totalVariation,coeff_single_mul_apply,one_mul]
  exact Equiv.sum_comp (Equiv.addLeft (-h)) (fun g => |x.coeff g|)


/-- Finite L¹ control for the self-convolution of a candidate even sum
support U, measured using the parity representation counts and A²−2U. -/
theorem even_support_bound (A B U:Measures G) (z:G) :
    totalVariation ((2 • U)^2-(2*mass (A^2)-Fintype.card G) • ones) ≤
      totalVariation (2 • U-A^2)*totalVariation (2 • U+A^2)+
      totalVariation (A^2+single z 1*B^2-(2:ℝ) • ones)*totalVariation (A^2)+
      totalVariation (A*B-ones)*totalVariation (A*B+ones) := by
  let central:Measures G:=(2*mass (A^2)-Fintype.card G) • ones
  have h:=variation_sub ((A^2+single z 1*B^2-(2:ℝ) • ones)*A^2)
    (single z 1*((A*B-ones)*(A*B+ones)))
  rw [←fourth_identity,shift_variation] at h
  have h1:totalVariation (A^4-central)≤
      totalVariation (A^2+single z 1*B^2-(2:ℝ) • ones)*totalVariation (A^2)+
      totalVariation (A*B-ones)*totalVariation (A*B+ones) :=
    h.trans (add_le_add (variation_product _ _) (variation_product _ _))
  have h2:totalVariation ((2 • U)^2-A^4)≤totalVariation (2 • U-A^2)*totalVariation (2 • U+A^2) := by
    rw [show (2 • U)^2-A^4=(2 • U-A^2)*(2 • U+A^2) by ring]
    exact variation_product _ _
  have plus (x y:Measures G):totalVariation (x+y)≤totalVariation x+totalVariation y := by
    simp only [totalVariation,coeff_add,Finsupp.add_apply,←sum_add_distrib]
    exact sum_le_sum fun g _ => abs_add_le _ _
  have bd:=plus ((2 • U)^2-A^4) (A^4-central)
  rw [sub_add_sub_cancel] at bd
  exact bd.trans (by linarith only [h1,h2])
#print axioms even_support_bound

variable [DecidableEq G]

/-- An L¹ bound about quarter density for self-sums gives a mean-square
bound for translate intersections via the exact centered energy identity. -/
theorem overlap_error (U:Finset G) :
    (∑ x,((Green33TailEnergy.diffReps U x:ℝ)-(Fintype.card G:ℝ)/4)^2) ≤
      (3*(Fintype.card G:ℝ)/4)*∑ x,|(Green33Multiplicity.reps U x:ℝ)-(Fintype.card G:ℝ)/4| := by
  rw [←Green33TailEnergy.centered_energy_eq,Finset.mul_sum]
  apply sum_le_sum
  intro x _
  have bound:Green33Multiplicity.reps U x≤Fintype.card G :=
    (show U.addConvolution U x≤U.card from addConvolution_le_card_left).trans (card_le_univ U)
  have non:=Nat.cast_nonneg (α:=ℝ) (Green33Multiplicity.reps U x)
  have hi:=Nat.cast_le (α:=ℝ).mpr bound
  have ab:|(Green33Multiplicity.reps U x:ℝ)-(Fintype.card G:ℝ)/4|≤3*(Fintype.card G:ℝ)/4 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  rw [←sq_abs (_-_),sq]
  exact mul_le_mul_of_nonneg_right ab (abs_nonneg _)
#print axioms overlap_error

end Green33ParityConvolution
