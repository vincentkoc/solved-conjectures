import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

/-! # The quartic whose six pairs model the sixth factorial gap -/

namespace Erdos478.TetrahedralGap
open Polynomial

noncomputable def quartic (R : Type*) [CommRing R] : R[X] := X^4-C 70*X^2-C 136*X+C 189

theorem quartic_monic (R : Type*) [CommRing R] [Nontrivial R] : (quartic R).Monic := by
  unfold quartic
  monicity <;> decide

theorem quartic_degree (R : Type*) [CommRing R] [Nontrivial R] : (quartic R).natDegree=4 := by
  unfold quartic
  compute_degree!

theorem quartic_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (quartic R).map f=quartic S := by simp [quartic, _root_.map_ofNat]

/-- The certificate works in characteristic zero and at every prime away
from the divisors of 1024 · 1957. -/
theorem quartic_separable (K : Type*) [Field K] (hn : (2003968 : K)≠0) : (quartic K).Separable := by
  let A : K[X] := 9184+952*X-404*X^2
  let B : K[X] := -1972-5831*X-238*X^2+101*X^3
  have cert : A*quartic K+B*derivative (quartic K)=C (2003968:K) := by
    simp [A,B,quartic,Polynomial.C_ofNat,Polynomial.derivative_mul]
    ring
  refine ⟨C ((2003968:K)⁻¹)*A,C ((2003968:K)⁻¹)*B,?_⟩
  calc
    _ = C ((2003968:K)⁻¹)*(A*quartic K+B*derivative (quartic K)) := by ring
    _ = 1 := by rw [cert,← map_mul,inv_mul_cancel₀ hn,map_one]

/-- The four sign choices with even sign parity have these four symmetric
functions whenever the square coordinates solve the sextic's cubic resolvent. -/
theorem quartic_factor {R : Type*} [CommRing R] {a b c : R}
    (sum : a^2+b^2+c^2=35) (pairs : a^2*b^2+a^2*c^2+b^2*c^2=259) (prod : a*b*c=17) :
    quartic R=(X-C (a+b+c))*(X-C (a-b-c))*(X-C (-a+b-c))*(X-C (-a-b+c)) := by
  calc
    quartic R = X^4-C (2*(a^2+b^2+c^2))*X^2-C (8*(a*b*c))*X+
      C ((a^2+b^2+c^2)^2-4*(a^2*b^2+a^2*c^2+b^2*c^2)) := by
        rw [sum,pairs,prod]; norm_num [quartic]
    _ = _ := by simp only [map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat]; ring

/-- For a pair of quartic roots let u be their sum, and v and w the
products in that pair and its complement. Their pairing yields the scaled
sixth gap polynomial. This identity also applies after regular reduction. -/
theorem pair_sextic {R : Type*} [CommRing R] (u v w : R) (sum : v+w=u^2-70)
    (skew : u*(w-v)=136) (prod : v*w=189) :
    (u+10)*(u+6)*(u+2)*(u-2)*(u-6)*(u-10)-4096=0 := by
  calc
    _ = u^2*((u^2-70)^2-4*189)-136^2 := by ring
    _ = u^2*((v+w)^2-4*(v*w))-(u*(w-v))^2 := by rw [sum,prod,skew]
    _ = 0 := by ring

#print axioms quartic
#print axioms quartic_monic
#print axioms quartic_degree
#print axioms quartic_map
#print axioms quartic_separable
#print axioms quartic_factor
#print axioms pair_sextic
end Erdos478.TetrahedralGap
