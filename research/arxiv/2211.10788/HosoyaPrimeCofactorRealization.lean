import HosoyaEvenFactorialReturns
import HosoyaPrimeIndexSieve
import HosoyaPrimePowerCofactors

/-! Exact index–value gcds in one residue of a Fibonacci return modulus. -/

namespace Arxiv.«2211.10788».IndexDivisors

/-- The gcd seen at a residue when the common divisors are restricted to A. -/
def residueGcd (A t : ℕ) : ℕ := (t.gcd A).gcd (lucasFibonacciSum t)

private lemma upper_gcd_congr {g A n t : ℕ} (hg : g ∣ Nat.fib A) (nt : n ≡ t [MOD A]) :
    g.gcd (lucasFibonacciSum n) = g.gcd (lucasFibonacciSum t) := by
  have eq := (upper_gcd_return A n).trans ((show n%A=t%A from nt) ▸ (upper_gcd_return A t).symm)
  have collapse (v : ℕ) : (v.gcd (Nat.fib A)).gcd g = v.gcd g := by
    rw [Nat.gcd_assoc,Nat.gcd_eq_right hg]
  simpa only [collapse,Nat.gcd_comm g] using congrArg (fun u => u.gcd g) eq

/-- A prime in the indicated cofactor class realizes the recorded gcd whenever it
avoids five and the two neighboring values at the fixed cofactor. -/
theorem prime_residue_formula {A : ℕ} (pos : 0 < A) (ret : A ∣ Nat.fib A) (t : ℕ)
    {q : ℕ} (hq : q.Prime) (h5 : q ≠ 5) (avoid : ¬q ∣ cofactorObstruction (t.gcd A))
    (cl : q ≡ t/(t.gcd A) [MOD A/(t.gcd A)]) :
    (t.gcd A)*q ≡ t [MOD A] ∧
      ((t.gcd A)*q).gcd (lucasFibonacciSum ((t.gcd A)*q)) = residueGcd A t := by
  let g := t.gcd A
  have gp : 0 < g := Nat.gcd_pos_of_pos_right _ pos
  have gA : g ∣ A := Nat.gcd_dvd_right ..
  have gL : g*(A/g)=A := Nat.mul_div_cancel' gA
  have gt : g*(t/g)=t := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  change q ≡ t/g [MOD A/g] at cl
  have hit : g*q ≡ t [MOD A] := by simpa only [gt,gL] using cl.mul_left' g
  have : Fact q.Prime := ⟨hq⟩
  have free : q.Coprime (lucasFibonacciSum (g*q)) := by
    apply hq.coprime_iff_not_dvd.mpr
    intro bad
    exact avoid (prime_dvd_cofactorObstruction (p:=q) h5 1 gp
      (by simpa only [pow_one,Nat.mul_comm q] using bad))
  exact ⟨hit,(Nat.Coprime.gcd_mul_right_cancel g free).trans (upper_gcd_congr (gA.trans ret) hit)⟩

/-- All primes beyond the explicit neighbor-product bound avoid the exceptional factors. -/
theorem large_prime_residue_formula {A : ℕ} (pos : 0 < A) (ret : A ∣ Nat.fib A) (t : ℕ)
    {q : ℕ} (hq : q.Prime) (big : max 5 (cofactorObstruction (t.gcd A)) < q)
    (cl : q ≡ t/(t.gcd A) [MOD A/(t.gcd A)]) :
    (t.gcd A)*q ≡ t [MOD A] ∧
      ((t.gcd A)*q).gcd (lucasFibonacciSum ((t.gcd A)*q)) = residueGcd A t :=
  prime_residue_formula pos ret t hq (by omega)
    (Nat.not_dvd_of_pos_of_lt (cofactorObstruction_pos (Nat.gcd_pos_of_pos_right _ pos)) (by omega)) cl

/-- Every residue has arbitrarily large prime-cofactor representatives attaining the
truncated gcd exactly, including the zero residue. -/
theorem prime_realizes_residue_gcd {A : ℕ} (pos : 0 < A) (ret : A ∣ Nat.fib A) (t B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ (t.gcd A)*q ≡ t [MOD A] ∧
      ((t.gcd A)*q).gcd (lucasFibonacciSum ((t.gcd A)*q)) = residueGcd A t := by
  let g := t.gcd A
  have gp : 0 < g := Nat.gcd_pos_of_pos_right _ pos
  have gA : g ∣ A := Nat.gcd_dvd_right ..
  have Lp : 0 < A/g := Nat.div_pos (Nat.le_of_dvd pos gA) gp
  have cop : (t/g).Coprime (A/g) := Nat.coprime_div_gcd_div_gcd gp
  obtain ⟨q,big,hq,cl⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max B (max 5 (cofactorObstruction g))) Lp.ne' cop
  exact ⟨q,by omega,hq,large_prime_residue_formula pos ret t hq (by
    change max 5 (cofactorObstruction g) < q
    omega) cl⟩

/-- Reduction of the index modulo a return modulus preserves the truncated gcd. -/
theorem residueGcd_mod {A : ℕ} (ret : A ∣ Nat.fib A) (n : ℕ) :
    residueGcd A (n%A) = A.gcd (n.gcd (lucasFibonacciSum n)) := by
  have he : n%A ≡ n [MOD A] := Nat.mod_modEq _ _
  unfold residueGcd
  rw [he.gcd_eq,upper_gcd_congr ((Nat.gcd_dvd_right n A).trans ret) he,
    Nat.gcd_comm n A,Nat.gcd_assoc]

#print axioms prime_residue_formula
#print axioms large_prime_residue_formula
#print axioms prime_realizes_residue_gcd
#print axioms residueGcd_mod

end Arxiv.«2211.10788».IndexDivisors
