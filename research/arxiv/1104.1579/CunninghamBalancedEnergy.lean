import CunninghamFiniteMultiplier
import CunninghamLinearReciprocalRoots

/-! The fixed multiplier isolates the leading coefficient at every index and for both signs. -/

namespace CunninghamChain.LinearRoots
open Polynomial CoefficientEnergy

private lemma balanced_telescoping (k : Bool) (a : ℤ) (n : ℕ) :
    (X-1)*polynomialTerm k (C a*X+C (-a)) n =
      X^n*C a*(X-1)^2+C (sign k)*(X^n-1) := by
  induction n with
  | zero => simp [polynomialTerm]; ring
  | succ n ih =>
    change (X-1)*(X*polynomialTerm k (C a*X+C (-a)) n+C (sign k))=_
    calc _ = X*((X-1)*polynomialTerm k (C a*X+C (-a)) n)+(X-1)*C (sign k) := by ring
         _ = _ := by rw [ih,pow_succ]; ring

set_option maxRecDepth 4096 in
/-- After multiplication by (X−1)K, the squared lower coefficients have total
less than one quarter the leading square. The bound is uniform in the index. -/
theorem balanced_tail_energy (k : Bool) {a : ℕ} (ha : 615 ≤ a) (n : ℕ) :
    let T := polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n
    let H := T*((X-1)*multiplier)
    4*energy H H.natDegree < H.leadingCoeff^2 := by
  let T := polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n
  let P := (X-1)^2*multiplier
  let H := T*((X-1)*multiplier)
  let seed : ℤ[X] := C (a:ℤ)*X+C (-(a:ℤ))
  have a0 : (a:ℤ)≠0 := by omega
  have sd : seed.natDegree=1 := natDegree_linear a0
  have shape := polynomialTerm_shape k seed (by omega) n
  have dt : T.natDegree=1+n := by simpa only [T,seed,sd] using shape.1
  have lt' : T.leadingCoeff=a := shape.2.trans (leadingCoeff_linear a0)
  have tn : T≠0 := leadingCoeff_ne_zero.mp (lt' ▸ a0)
  have kn : multiplier≠0 := by intro h; have := multiplier_shape.2; simp [h] at this
  have xm : (X-1:ℤ[X])≠0 := by simpa using X_sub_C_ne_zero (1:ℤ)
  have xmdeg : (X-1:ℤ[X]).natDegree=1 := by simpa using natDegree_X_sub_C (1:ℤ)
  have xmlc : (X-1:ℤ[X]).leadingCoeff=1 := by simpa using (monic_X_sub_C (1:ℤ)).leadingCoeff
  have dH : H.natDegree=n+64 := by
    rw [show H=T*((X-1)*multiplier) from rfl,natDegree_mul tn (mul_ne_zero xm kn),
      natDegree_mul xm kn,xmdeg,multiplier_shape.1,dt]
    omega
  have lH : H.leadingCoeff=(a:ℤ)*32 := by
    rw [show H=T*((X-1)*multiplier) from rfl,leadingCoeff_mul,leadingCoeff_mul,
      xmlc,one_mul,lt',multiplier_shape.2]
  have expr : H=X^n*(C (a:ℤ)*P)+C (sign k)*(X^n*multiplier-multiplier) := by
    calc H = ((X-1)*T)*multiplier := by dsimp [H]; ring
         _ = _ := by rw [show (X-1)*T=_ from balanced_telescoping k (a:ℤ) n]; dsimp [P]; ring
  have main : energy (X^n*(C (a:ℤ)*P)) (n+64)=(a:ℤ)^2*96 := by
    rw [energy_shift,energy_scale,multiplier_energy.2]
  have ek := multiplier_energy.1
  have kd := multiplier_shape.1
  have err := energy_sub (X^n*multiplier) multiplier (n+64)
  rw [energy_shift,energy_stable multiplier (N:=64) (by omega : multiplier.natDegree<64) (by omega : 64≤n+64),ek] at err
  have plus := energy_add (X^n*(C (a:ℤ)*P)) (C (sign k)*(X^n*multiplier-multiplier)) (n+64)
  have eps : (sign k)^2=1 := by cases k <;> decide
  rw [←expr,main,energy_scale,eps,one_mul] at plus
  change 4*energy H H.natDegree < H.leadingCoeff^2
  rw [dH,lH]
  have big : (615:ℤ)^2 ≤ (a:ℤ)^2 := pow_le_pow_left₀ (by decide) (by omega) _
  nlinarith

#print axioms balanced_tail_energy

end CunninghamChain.LinearRoots
