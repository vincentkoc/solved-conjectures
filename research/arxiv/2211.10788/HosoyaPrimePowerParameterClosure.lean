import HosoyaPowerIndexClosure

/-! Exact ordinary and cofinal congruence tests at powers of prime or
almost-prime parameters on the upper Hosoya diagonal. -/

namespace Arxiv.«2211.10788».PowerIndex
open AlmostPrimeClosure CongruenceClosure ProgressionClosure
open scoped ArithmeticFunction.Omega

/-- A modular test that can be met at arbitrarily large bases with
exactly k prime factors has a signed base with strictly fewer factors. -/
theorem almost_prime_power_cofinal_iff {d r e k E : ℕ} (hd : 0 < d) (ep : 0 < e)
    (pe : 0 < E) (y : ℤ) :
    (∀ M : ℕ, 0 < M → M.Coprime E → ∀ B : ℕ, ∃ n : ℕ, B<n ∧
      Nat.IsAlmostPrime k n ∧ Hit d r M y (n^e)) ↔
    ∃ v : ℤ, v≠0 ∧ Ω v.natAbs<k ∧ signed (r+d*v^e)=y := by
  constructor
  · intro all
    let B := y.natAbs+r+2
    let D := 4*B.factorial^2
    have dp : 0 < D := by dsimp [D]; positivity
    obtain ⟨M,mp,unit,conf⟩ := confining_modulus (k:=e*k) (r:=r) hd pe dp y
    obtain ⟨n,big,weight,hit⟩ := all M mp unit B
    have bign : B<n^e := big.trans_le (Nat.le_self_pow ep.ne' n)
    have scaled : Nat.IsAlmostPrime (e*k) (n^e) :=
      ⟨pow_ne_zero _ weight.1,by rw [ArithmeticFunction.cardFactors_pow,weight.2]⟩
    obtain ⟨w,cl,nz,budget,val⟩ := conf (n^e) bign scaled hit
    have small : w.natAbs≤B := by simpa only [B,val] using parameter_bound r hd w
    obtain ⟨v,hv⟩ := bounded_power_test B (t:=(n:ℤ)) ep small (by simpa only [D,Nat.cast_pow] using cl)
    rw [hv,Int.natAbs_pow,ArithmeticFunction.cardFactors_pow] at budget
    refine ⟨v,?_,Nat.lt_of_mul_lt_mul_left budget,hv ▸ val⟩
    rintro rfl
    simp [ep.ne'] at hv
    exact nz hv
  · rintro ⟨v,nz,budget,val⟩ M mp _ B
    exact hits_of_approximable_base ep val (fun _ tp => large_almost_prime_congruent nz budget tp) mp B

/-- At a fixed total prime-factor count the remaining modular hits
are precisely the values actually attained. -/
theorem almost_prime_power_modular_iff {d r e k E : ℕ} (hd : 0 < d) (ep : 0 < e)
    (pe : 0 < E) (y : ℤ) :
    (∀ M : ℕ, 0 < M → M.Coprime E → ∃ n : ℕ, Nat.IsAlmostPrime k n ∧ Hit d r M y (n^e)) ↔
    (∃ n : ℕ, Nat.IsAlmostPrime k n ∧ (lucasFibonacciSum (r+d*n^e):ℤ)=y) ∨
      ∃ v : ℤ, v≠0 ∧ Ω v.natAbs<k ∧ signed (r+d*v^e)=y := by
  rw [restricted_modular_hits_iff (fun n : ℕ => n^e) (fun _ _ h => Nat.pow_le_pow_left h e)
    (Nat.IsAlmostPrime k) pe y, almost_prime_power_cofinal_iff hd ep pe y]

private theorem small_base (w : ℤ) (nz : w≠0) (small : Ω w.natAbs<1) : w=1 ∨ w= -1 := by
  have z := ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp (show Ω w.natAbs=0 by omega)
  omega

/-- For a prime-valued candidate, the only additional modular solution
is 3, and it occurs precisely at odd exponents. In particular every
prime candidate at prime-square indices is detected exactly. -/
theorem prime_at_prime_powers_iff {e E q : ℕ} (ep : 0 < e) (pe : 0 < E) (qp : q.Prime) :
    (∀ M : ℕ, 0 < M → M.Coprime E → ∃ p : ℕ, p.Prime ∧ lucasFibonacciSum (p^e) ≡ q [MOD M]) ↔
      (Odd e ∧ q=3) ∨ ∃ p : ℕ, p.Prime ∧ lucasFibonacciSum (p^e)=q := by
  have base := almost_prime_power_modular_iff (r:=0) (d:=1) (k:=1) (by decide) ep pe (q:ℤ)
  simp only [Nat.isAlmostPrime_one_iff,Hit,one_mul,zero_add,Nat.cast_zero,Nat.cast_one,
    Int.natCast_modEq_iff,Nat.cast_inj] at base
  have four : signed (1:ℤ)=4 := by decide
  have three : signed (-1:ℤ)=3 := by decide
  have nf : q≠4 := by rintro rfl; norm_num at qp
  constructor
  · intro tested
    rcases base.mp tested with actual|⟨v,nz,small,val⟩
    · exact Or.inr actual
    rcases small_base v nz small with rfl|rfl
    · rw [one_pow,four] at val
      omega
    · rcases Nat.even_or_odd e with ev|od
      · rw [ev.neg_one_pow,four] at val
        omega
      · rw [od.neg_one_pow,three] at val
        exact Or.inl ⟨od,by omega⟩
  · rintro (⟨od,rfl⟩|actual)
    · apply base.mpr
      exact Or.inr ⟨-1,by decide,by simp,by rw [od.neg_one_pow,three]; rfl⟩
    · exact base.mpr (Or.inl actual)

#print axioms almost_prime_power_cofinal_iff
#print axioms almost_prime_power_modular_iff
#print axioms prime_at_prime_powers_iff

end Arxiv.«2211.10788».PowerIndex
