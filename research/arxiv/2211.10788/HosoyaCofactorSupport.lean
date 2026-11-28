import HosoyaPrimePowerCofactors
import LucasFibonacciSelfDividingPrimePowers

/-! Effective finiteness for self-dividing upper indices with one unrestricted prime. -/

namespace Arxiv.«2211.10788».IndexDivisors

/-- The product bounding the smooth part uses the local rank coefficients. -/
def smoothBound (S : Finset ℕ) : ℕ := ∏ p ∈ S, supportCoefficient p

/-- Only primes of the original support or of a cofactor obstruction can
occur when the index permits a single prime outside the support. -/
def enlargedSupport (S : Finset ℕ) : Finset ℕ :=
  S ∪ (smoothBound S).divisors.biUnion (fun m => (cofactorObstruction m).primeFactors)

/-- Removing the unique prime outside S leaves an S-smooth cofactor. -/
lemma cofactor_supported {n p : ℕ} {S : Finset ℕ} (hp : p ∈ n.primeFactors \ S)
    (one : (n.primeFactors \ S).card≤1) : (ordCompl[p] n).primeFactors ⊆ S := by
  obtain ⟨prime,_,hn⟩ := Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1
  have md := Nat.ordCompl_dvd n p
  intro q hq
  obtain ⟨qp,qd,_⟩ := Nat.mem_primeFactors.mp hq
  by_contra out
  have qe := Finset.card_le_one_iff.mp one (Finset.mem_sdiff.mpr ⟨qp.mem_primeFactors (qd.trans md) hn,out⟩) hp
  exact Nat.not_dvd_ordCompl prime hn (qe ▸ qd)

/-- The p-free cofactor of a self-dividing index at its unique prime
outside S is a divisor of the previously established smooth bound. -/
theorem self_cofactor_dvd {n p : ℕ} {S : Finset ℕ} (h : n ∣ lucasFibonacciSum n)
    (hp : p ∈ n.primeFactors \ S) (one : (n.primeFactors \ S).card≤1) :
    ordCompl[p] n ∣ smoothBound S := by
  have md := Nat.ordCompl_dvd n p
  exact (smooth_common_divisor_bound S).2 n _ (Nat.dvd_gcd md (md.trans h)) (cofactor_supported hp one)

/-- Every such index divides one explicit positive integer depending only on S. -/
theorem one_outside_self_divisor_bound (S : Finset ℕ) :
    0 < smoothBound (enlargedSupport S) ∧ ∀ n : ℕ, n ∣ lucasFibonacciSum n →
      (n.primeFactors \ S).card≤1 → n ∣ smoothBound (enlargedSupport S) := by
  refine ⟨(smooth_common_divisor_bound _).1,?_⟩
  intro n h one
  apply (smooth_common_divisor_bound _).2 n n (Nat.dvd_gcd dvd_rfl h)
  intro p hp
  by_cases inside : p ∈ S
  · exact Finset.mem_union_left _ inside
  apply Finset.mem_union_right
  let m := ordCompl[p] n
  obtain ⟨prime,div,hn⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨prime⟩
  have hm : 0 < m := Nat.ordCompl_pos p hn
  have he : p^n.factorization p*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
  have h5 : p≠5 := ((attainable_index_value_power (p:=p) 0).mp
    ⟨n,by simpa using Nat.dvd_gcd div (div.trans h)⟩).1
  apply Finset.mem_biUnion.mpr
  refine ⟨m,Nat.mem_divisors.mpr ⟨self_cofactor_dvd h (Finset.mem_sdiff.mpr ⟨hp,inside⟩) one,
    (smooth_common_divisor_bound S).1.ne'⟩,prime.mem_primeFactors ?_ (cofactorObstruction_pos hm).ne'⟩
  apply prime_dvd_cofactorObstruction h5 (n.factorization p) hm
  rw [he]
  exact div.trans h

/-- Allowing one arbitrary prime beyond any finite support still leaves
only finitely many indices that divide their own upper value. -/
theorem finite_one_outside_self_divisors (S : Finset ℕ) :
    {n : ℕ | n ∣ lucasFibonacciSum n ∧ (n.primeFactors \ S).card≤1}.Finite := by
  obtain ⟨pos,bound⟩ := one_outside_self_divisor_bound S
  apply (Finset.finite_toSet (smoothBound (enlargedSupport S)).divisors).subset
  intro n h
  exact Nat.mem_divisors.mpr ⟨bound n h.1 h.2,pos.ne'⟩

#print axioms self_cofactor_dvd
#print axioms one_outside_self_divisor_bound
#print axioms finite_one_outside_self_divisors

end Arxiv.«2211.10788».IndexDivisors
