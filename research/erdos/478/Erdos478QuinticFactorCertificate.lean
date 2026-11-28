import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-! # Explicit factorizations of the first four gap polynomials modulo 9209

Each polynomial identity follows by exhibiting the multiple of 9209 in its
integer expansion. Euler’s criterion excludes roots of the residual quadratic.
-/

namespace Erdos478.QuinticSample

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

local instance : Fact (Nat.Prime 9209) := ⟨by norm_num1⟩

private theorem modulus : (9209 : ZMod 9209)=0 := by decide +kernel

theorem factor2 (x : ZMod 9209) : x*(x-1)-1=
    (x-750)*(x-8460) := by
  linear_combination (x - 689)*modulus

theorem factor3 (x : ZMod 9209) : x*(x-1)*(x-2)-1=
    (x-4868)*(x-6407)*(x-7146) := by
  linear_combination (2*x^2 - 12136*x + 24202255)*modulus

theorem factor4 (x : ZMod 9209) : x*(x-1)*(x-2)*(x-3)-1=
    (x-488)*(x-771)*(x-8441)*(x-8724) := by
  linear_combination (2*x^3 - 10384*x^2 + 10768830*x - 3008647337)*modulus

theorem factor5 (x : ZMod 9209) : x*(x-1)*(x-2)*(x-3)*(x-4)-1=
    (x-987)*(x-5706)*(x-6091)*(x^2+3565*x+4920) := by
  linear_combination (x^4 - 90*x^3 - 14230177*x^2 + 13254798306*x + 18326948071)*modulus

theorem quadratic_nonzero (x : ZMod 9209) : x^2+3565*x+4920≠0 := by
  intro h
  have cert : ¬IsSquare (8752 : ZMod 9209) := by
    rw [ZMod.euler_criterion (p:=9209) (by decide)]
    decide +kernel
  apply cert
  refine ⟨2*x+3565,?_⟩
  linear_combination -4*h - 1377*modulus

#print axioms factor2
#print axioms factor3
#print axioms factor4
#print axioms factor5
#print axioms quadratic_nonzero
end Erdos478.QuinticSample