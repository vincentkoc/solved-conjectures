import HosoyaPrimePowerIndices

/-! Frobenius expresses the upper Hosoya value at a prime-power multiple in terms of the cofactor. -/

namespace Arxiv.«2211.10788».IndexDivisors

private abbrev FAlg (p : ℕ) := QuadraticAlgebra (ZMod p) 1 1
private abbrev gen (p : ℕ) : FAlg p := QuadraticAlgebra.omega
private def weight {p : ℕ} (z : FAlg p) : ZMod p := z.re+4*z.im

private lemma gen_sq (p : ℕ) : (gen p)^2=gen p+1 := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [gen,add_comm]

private lemma weight_step {p : ℕ} (z : FAlg p) (hz : z^2=z+1) (t : ℕ) :
    weight (z^(t+2))=weight (z^(t+1))+weight (z^t) := by
  rw [pow_add,hz,mul_add,mul_one,pow_succ]
  simp [weight]
  ring

private lemma weight_gen (p n : ℕ) : weight (gen p^n)=(lucasFibonacciSum n:ZMod p) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [weight,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,lucas_fibonacci_sum_zero]
  | one => simp [gen,weight,lucas_fibonacci_sum_one]
  | more i h₀ h₁ => rw [weight_step _ (gen_sq p),h₀,h₁,lucas_fibonacci_sum_recurrence,Nat.cast_add]

/-- Decimation by pᵉ retains the Fibonacci recurrence modulo p. Its first
two values give the displayed interpolation, including at the ramified prime. -/
theorem upper_prime_power_cofactor {p : ℕ} [Fact p.Prime] (e m : ℕ) :
    (lucasFibonacciSum (p^e*m) : ZMod p) =
      (lucasFibonacciSum m : ZMod p)+((lucasFibonacciSum (p^e):ZMod p)-4)*Nat.fib m := by
  let : CharP (FAlg p) p := charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  have hpow : (gen p^(p^e))^2=gen p^(p^e)+1 := by
    have h := congrArg (iterateFrobenius (FAlg p) p e) (gen_sq p)
    simpa only [map_pow,map_add,map_one,iterateFrobenius_def] using h
  have stride (t : ℕ) : (lucasFibonacciSum (p^e*(t+2)):ZMod p)=
      (lucasFibonacciSum (p^e*(t+1)):ZMod p)+(lucasFibonacciSum (p^e*t):ZMod p) := by
    simpa only [←pow_mul,weight_gen] using weight_step _ hpow t
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp [lucas_fibonacci_sum_one]
  | more m h₀ h₁ =>
    rw [stride,h₀,h₁,lucas_fibonacci_sum_recurrence,Nat.fib_add_two]
    push_cast
    ring

/-- For odd p the residue of every decimated term is explicit in the
cofactor and the Euler-criterion power of 5. This includes p=5. -/
theorem upper_odd_prime_cofactor {p : ℕ} [Fact p.Prime] (odd : p≠2) (e m : ℕ) :
    2*(lucasFibonacciSum (p^e*m):ZMod p)=2*(lucasFibonacciSum m:ZMod p)+
      7*((5^(p/2):ZMod p)^e-1)*Nat.fib m := by
  let : CharP (FAlg p) p := charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  let u := gen p
  let D : FAlg p := 2*u-1
  let s := p/2
  have parity : p=2*s+1 := by
    obtain ⟨t,h⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
    dsimp only [s]
    omega
  have dsq : D^2=5 := by dsimp [D,u]; linear_combination 4*(gen_sq p)
  have dp : frobenius (FAlg p) p D=(5:FAlg p)^s*D := by
    change D^p=_
    calc D^p=D^(2*s+1) := congrArg (D^·) parity
         _ = _ := by rw [pow_succ,pow_mul,dsq]
  have iter (j : ℕ) : D^(p^j)=((5:FAlg p)^s)^j*D := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc D^(p^(j+1)) = frobenius (FAlg p) p (D^(p^j)) := by rw [frobenius_def,←pow_mul,pow_succ]
           _ = _ := by rw [ih,map_mul,map_pow,map_pow,map_ofNat,dp,pow_succ]; ring
  have phi : (2:FAlg p)*u^(p^e)-1=((5:FAlg p)^s)^e*D := by
    have h : iterateFrobenius (FAlg p) p e D=_ := iter e
    simpa only [D,map_sub,map_mul,map_ofNat,map_one,iterateFrobenius_def] using h
  have coords : (2:ZMod p)*weight (u^(p^e))-1=((5:ZMod p)^s)^e*7 := by
    let A := algebraMap (ZMod p) (FAlg p)
    have c : ((5:FAlg p)^s)^e=A (((5:ZMod p)^s)^e)  := by simp only [A,map_pow,map_ofNat]
    rw [c] at phi
    change (2:ZMod p)*((u^(p^e)).re+4*(u^(p^e)).im)-1=_
    have h := congrArg (fun z : FAlg p => z.re+4*z.im) phi
    simp only [D,u,gen,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
      QuadraticAlgebra.omega_re,QuadraticAlgebra.omega_im,A,QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im] at h
    linear_combination h
  change (2:ZMod p)*weight (gen p^(p^e))-1=_ at coords
  rw [weight_gen] at coords
  rw [upper_prime_power_cofactor]
  dsimp [s] at coords
  linear_combination (Nat.fib m:ZMod p)*coords

/-- At a positive cofactor m this product is the upper value times its
lower neighbor. It bounds the possible prime base of a self-dividing tower. -/
def cofactorObstruction (m : ℕ) : ℕ :=
  lucasFibonacciSum m*(7*Nat.fib m-lucasFibonacciSum m)

private lemma below_seven {m : ℕ} (hm : 0 < m) :
    lucasFibonacciSum m < 7*Nat.fib m := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have pos := Nat.fib_pos.mpr hm
  have lo := Nat.fib_le_fib_succ (n:=j)
  simp only [Nat.succ_eq_add_one] at pos ⊢
  simp only [lucasFibonacciSum,Nat.fib_add_two]
  omega

theorem cofactorObstruction_pos {m : ℕ} (hm : 0 < m) : 0 < cofactorObstruction m := by
  have hp := Nat.fib_pos.mpr hm
  have hu : 0 < lucasFibonacciSum m := by unfold lucasFibonacciSum; omega
  exact Nat.mul_pos hu (Nat.sub_pos_of_lt (below_seven hm))

/-- Removal of the full prime power from the index leaves a necessary
divisor of a fixed neighbor product evaluated only at the cofactor. -/
theorem prime_dvd_cofactorObstruction {p : ℕ} [Fact p.Prime] (h5 : p≠5) (e : ℕ) {m : ℕ}
    (hm : 0 < m) (dvd : p ∣ lucasFibonacciSum (p^e*m)) : p ∣ cofactorObstruction m := by
  have H := upper_prime_power_cofactor (p:=p) e m
  rw [(ZMod.natCast_eq_zero_iff ..).mpr dvd] at H
  unfold cofactorObstruction
  rcases upper_prime_power_residues h5 e with pos|neg
  · refine dvd_mul_of_dvd_left ?_ _
    apply (ZMod.natCast_eq_zero_iff ..).mp
    simpa [pos] using H.symm
  · refine dvd_mul_of_dvd_right ?_ _
    apply (ZMod.natCast_eq_zero_iff ..).mp
    rw [neg] at H
    rw [Nat.cast_sub (below_seven hm).le,Nat.cast_mul,Nat.cast_ofNat]
    linear_combination H

#print axioms upper_prime_power_cofactor
#print axioms upper_odd_prime_cofactor
#print axioms cofactorObstruction_pos
#print axioms prime_dvd_cofactorObstruction

end Arxiv.«2211.10788».IndexDivisors
