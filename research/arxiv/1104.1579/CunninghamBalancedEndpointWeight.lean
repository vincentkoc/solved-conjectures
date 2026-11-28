import CunninghamBalancedGapQuadratic

/-! Closed coefficient weights for both balanced quadratic endpoints. -/

namespace CunninghamChain.GapLift
open Polynomial CoefficientEnergy LinearRoots LargeGap

def balancedWeight (a : ℕ) (k : Bool) : ℕ :=
  1+5*a^2+(if k then a+1 else a-1)^2

lemma balanced_endpoint_degree {a : ℕ} (ha : 2≤a) (k : Bool) : (gapEndpoint a k).natDegree=2 := by
  have nz : -sign k ≠ 0 := by cases k <;> decide
  rw [gapEndpoint,natDegree_C_mul nz,(quadratic_ends ha k).2.2]

theorem balanced_endpoint_weight {a : ℕ} (ha : 2≤a) (k : Bool) :
    (1+energy (gapEndpoint a k) ((gapEndpoint a k).natDegree+1)).toNat=balancedWeight a k := by
  obtain ⟨lo,hi,deg⟩ := quadratic_ends ha k
  have mid : (gapQuadratic a k).coeff 1 = -(2*(a:ℤ)) := by
    simp only [gapQuadratic,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
    norm_num
  rw [balanced_endpoint_degree ha]
  have eq : (1+energy (gapEndpoint a k) 3 : ℤ)=(balancedWeight a k : ℤ) := by
    simp only [energy,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      gapEndpoint,coeff_C_mul,lo,hi,mid]
    cases k <;> simp [sign,balancedWeight,Nat.cast_sub (by omega : 1≤a)] <;> ring
  rw [eq,Int.toNat_natCast]

theorem gapThreshold_eq {a : ℕ} (ha : 2≤a) (k : Bool) :
    gapThreshold (gapEndpoint a k)=12*4^(balancedWeight a k) := by
  unfold gapThreshold
  rw [balanced_endpoint_weight ha,balanced_endpoint_degree ha]
  rw [pow_succ,show (4:ℕ)=(2:ℕ)^2 by decide,←pow_mul]
  ring

#print axioms balanced_endpoint_weight
#print axioms gapThreshold_eq

end CunninghamChain.GapLift
