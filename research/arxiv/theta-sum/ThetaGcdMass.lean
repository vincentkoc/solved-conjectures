import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! The divisor expansion and prime-power values of Pillai's gcd sum. -/
namespace Arxiv.«2501.03234».ThetaCompositeFourier
open Finset

/-- Pillai's gcd sum, including the last endpoint. -/
def gcdMass (k : ℕ) : ℕ := ∑ j∈range k,(j+1).gcd k

/-- Divisor convolution of Euler's totient with the identity function. -/
theorem gcdMass_divisors (k : ℕ) :
    gcdMass k=∑ d∈k.divisors,d.totient*(k/d) := by
  by_cases hk : k=0
  · simp [hk,gcdMass]
  classical
  have H (j : ℕ) : (j+1).gcd k=∑ d∈k.divisors,if d∣j+1 then d.totient else 0 := by
    have hs : ((j+1).gcd k).divisors=k.divisors.filter (·∣j+1) := by
      ext d
      have hpos := Nat.gcd_pos_of_pos_left k (Nat.succ_pos j)
      simp [Nat.mem_divisors,hpos.ne',hk,Nat.dvd_gcd_iff,and_comm]
    rw [←Nat.sum_totient ((j+1).gcd k),hs,sum_filter]
  unfold gcdMass
  simp_rw [H]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [←sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul,Nat.cast_id,mul_comm]

private def phi : ArithmeticFunction ℕ := ⟨Nat.totient,Nat.totient_zero⟩
private lemma mass_eq (k : ℕ) : gcdMass k=(phi*ArithmeticFunction.id) k := by
  rw [gcdMass_divisors,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => phi a * ArithmeticFunction.id b)]
  rfl

theorem gcdMass_mul {m n : ℕ} (h : m.Coprime n) : gcdMass (m*n)=gcdMass m*gcdMass n := by
  have hφ : phi.IsMultiplicative := ⟨Nat.totient_one,fun hc => Nat.totient_mul hc⟩
  simpa only [mass_eq] using (hφ.mul ArithmeticFunction.isMultiplicative_id).map_mul_of_coprime h

private theorem gcdMass_prime_succ {p : ℕ} (hp : p.Prime) (n : ℕ) :
    gcdMass (p^(n+1))=p^(n+1)+(n+1)*p^n*(p-1) := by
  rw [gcdMass_divisors,Nat.sum_divisors_prime_pow hp,sum_range_succ']
  have H (i : ℕ) (hi : i∈range (n+1)) :
      (p^(i+1)).totient*(p^(n+1)/p^(i+1))=p^n*(p-1) := by
    have hi' := mem_range.mp hi
    have hd : p^(n+1)/p^(i+1)=p^(n-i) := by
      conv_lhs => lhs; rw [show n+1=(n-i)+(i+1) by omega,pow_add]
      exact Nat.mul_div_cancel _ (pow_pos hp.pos _)
    rw [Nat.totient_prime_pow_succ hp,hd]
    calc _ = (p^i*p^(n-i))*(p-1) := by ring
         _ = _ := by rw [←pow_add,show i+(n-i)=n by omega]
  rw [sum_congr rfl H]
  simp [mul_assoc,add_comm]

theorem gcdMass_prime_power {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (gcdMass (p^n):ℝ)/(p:ℝ)^n=1+n*(1-1/(p:ℝ)) := by
  cases n with
  | zero => simp [gcdMass]
  | succ n =>
    rw [gcdMass_prime_succ hp]
    have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
    push_cast [Nat.cast_sub hp.one_le]
    rw [pow_succ]
    field_simp

/-- The normalized singular mass on powers of a fixed base is a polynomial in n. -/
theorem gcdMass_power_product {a : ℕ} (ha : a≠0) (n : ℕ) :
    (gcdMass (a^n):ℝ)/(a:ℝ)^n=∏ p∈a.primeFactors,
      (1+(n:ℝ)*(a.factorization p:ℝ)*(1-1/(p:ℝ))) := by
  let f (x : ℕ) : ℝ := (gcdMass (x^n):ℝ)/(x:ℝ)^n
  have hmul (x y : ℕ) (hc : x.Coprime y) : f (x*y)=f x*f y := by
    simp only [f,Nat.cast_mul,mul_pow,gcdMass_mul ((hc.pow_left n).pow_right n),Nat.cast_mul]
    ring
  have H := Nat.multiplicative_factorization f hmul (by simp [f,gcdMass]) ha
  change f a=∏ p∈a.primeFactors,f (p^a.factorization p) at H
  apply H.trans
  apply prod_congr rfl
  intro p hp
  simp only [f,Nat.cast_pow,←pow_mul]
  rw [gcdMass_prime_power (Nat.prime_of_mem_primeFactors hp)]
  push_cast
  ring

#print axioms gcdMass_power_product

#print axioms gcdMass_divisors
#print axioms gcdMass_mul
#print axioms gcdMass_prime_power
end Arxiv.«2501.03234».ThetaCompositeFourier
