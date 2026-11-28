import HosoyaPrimePowerCofactors
import LucasFibonacciSelfDividingPrimePowers

/-! An exact cofactor criterion for an upper Hosoya index to divide its value. -/

namespace Arxiv.«2211.10788».IndexDivisors

lemma two_dvd_upper_iff (n : ℕ) : 2 ∣ lucasFibonacciSum n ↔ n%3=1 := by
  have per : Function.Periodic (fun i => lucasFibonacciSum i%2) 3 := by
    intro i
    change lucasFibonacciSum ((i+1)+2)%2=lucasFibonacciSum i%2
    rw [lucas_fibonacci_sum_recurrence,show i+1+1=i+2 by omega,lucas_fibonacci_sum_recurrence]
    omega
  have h := per.nat_mul (n/3) (n%3)
  change lucasFibonacciSum (n%3+n/3*3)%2=_ at h
  rw [Nat.mul_comm (n/3),Nat.mod_add_div] at h
  rw [Nat.dvd_iff_mod_eq_zero,h]
  have lt := Nat.mod_lt n (by decide : 0<3)
  generalize n%3=r at *
  interval_cases r <;> decide

/-- The p-part is tested at its p-free cofactor and at a fixed rank coefficient.
For p=2 the prime-level obstruction is the residue of the index modulo three. -/
def localCofactorTest (n p : ℕ) : Prop :=
  let e := n.factorization p
  let m := ordCompl[p] n
  p≠5 ∧ p^e ∣ supportCoefficient p ∧
    (if p=2 then n%3=1 else
      2*(lucasFibonacciSum m:ZMod p)+7*((5^(p/2):ZMod p)^e-1)*Nat.fib m=0)

theorem prime_part_iff_cofactor_test {n p : ℕ} (mem : p ∈ n.primeFactors) :
    ordProj[p] n ∣ lucasFibonacciSum n ↔ localCofactorTest n p := by
  obtain ⟨prime,div,hn⟩ := Nat.mem_primeFactors.mp mem
  have : Fact p.Prime := ⟨prime⟩
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (prime.factorization_pos_of_dvd hn div).ne'
  have dj : p^(j+1) ∣ n := by simpa only [hj] using Nat.ordProj_dvd n p
  have hres : (p ∣ lucasFibonacciSum n) ↔
      (if p=2 then n%3=1 else
        2*(lucasFibonacciSum (ordCompl[p] n):ZMod p)+
          7*((5^(p/2):ZMod p)^n.factorization p-1)*Nat.fib (ordCompl[p] n)=0) := by
    split_ifs with h2
    · subst p; exact two_dvd_upper_iff n
    have nz : (2:ZMod p)≠0 := by
      intro bad
      have div2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using bad)
      exact h2 ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp div2)
    rw [←upper_odd_prime_cofactor h2,Nat.ordProj_mul_ordCompl_eq_self,
      mul_eq_zero,or_iff_right nz,ZMod.natCast_eq_zero_iff]
  unfold localCofactorTest
  dsimp only
  rw [←hres]
  simp only [hj,supportCoefficient,dif_pos prime]
  constructor
  · intro h
    have gl := (attainable_index_value_power (p:=p) j).mp ⟨n,Nat.dvd_gcd dj h⟩
    exact ⟨gl.1,gl.2.2,(dvd_pow_self _ (by omega : j+1≠0)).trans h⟩
  · rintro ⟨h5,cap,hit⟩
    exact (upper_divisor_on_tower (p:=p) h5 ((pow_dvd_pow p (by omega : j≤j+1)).trans dj)).mpr ⟨hit,cap⟩

/-- For every positive n, self-divisibility is equivalent to independent
tests on its prime powers, using the proper cofactor for every odd base. -/
theorem self_divides_iff_local_cofactors {n : ℕ} (hn : 0 < n) :
    n ∣ lucasFibonacciSum n ↔ ∀ p ∈ n.primeFactors, localCofactorTest n p := by
  constructor
  · intro h p mem
    exact (prime_part_iff_cofactor_test mem).mp ((Nat.ordProj_dvd n p).trans h)
  intro h
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hd
  by_cases hk : k=0
  · simp [hk]
  have mem := hp.mem_primeFactors ((dvd_pow_self _ hk).trans hd) hn.ne'
  exact ((hp.pow_dvd_iff_dvd_ordProj hn.ne').mp hd).trans ((prime_part_iff_cofactor_test mem).mpr (h _ mem))

#print axioms prime_part_iff_cofactor_test
#print axioms self_divides_iff_local_cofactors

end Arxiv.«2211.10788».IndexDivisors
