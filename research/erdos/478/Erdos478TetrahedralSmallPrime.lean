import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # A small simultaneous residue certificate for the tetrahedral quartic -/

namespace Erdos478.TetrahedralSample
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem modulus : (1439 : ZMod 1439)=0 := by decide +kernel

theorem gap_two (x : ZMod 1439) : x*(x-1)-1=(x-701)*(x-739) := by
  linear_combination (x-360)*modulus

theorem cubic_nonzero : ∀ x : ZMod 1439, x*(x-1)*(x-2)-1≠0 := by decide +kernel

theorem gap_four (x : ZMod 1439) : x*(x-1)*(x-2)*(x-3)-1=
    (x-50)*(x-333)*(x-1109)*(x-1392) := by
  linear_combination (2*x^3-1750*x^2+439812*x-17861759)*modulus

theorem gap_five (x : ZMod 1439) : x*(x-1)*(x-2)*(x-3)*(x-4)-1=
    (x-68)*(x-743)*(x^3+801*x^2+498*x+181) := by
  linear_combination (416*x^3-27843*x^2-17383*x-6355)*modulus

theorem quintic_factor_nonzero : ∀ x : ZMod 1439, x^3+801*x^2+498*x+181≠0 := by decide +kernel

theorem quartic_split (x : ZMod 1439) : x^4-70*x^2-136*x+189=
    (x-1131)*(x-1331)*(x^2+1023*x+139) := by
  linear_combination (x^3+704*x^2-1069939*x-145410)*modulus

theorem quadratic_nonzero : ∀ x : ZMod 1439, x^2+1023*x+139≠0 := by decide +kernel

#print axioms gap_two
#print axioms cubic_nonzero
#print axioms gap_four
#print axioms gap_five
#print axioms quintic_factor_nonzero
#print axioms quartic_split
#print axioms quadratic_nonzero
end Erdos478.TetrahedralSample
