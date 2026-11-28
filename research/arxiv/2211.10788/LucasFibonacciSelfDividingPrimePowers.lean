import HosoyaIndexCommonDivisors

/-! Finite support bounds and the prime-power indices dividing their own upper values. -/

namespace Arxiv.«2211.10788».IndexDivisors

/-- Integer used to bound the p-part of every common divisor. Values at
nonprimes contribute the neutral factor to products over a finite support. -/
def supportCoefficient (p : ℕ) : ℕ :=
  if h : p.Prime then @rankCoefficient p ⟨h.ne_zero⟩ else 1

/-- Every divisor of the index and its value supported on S divides one
explicit positive integer. In particular, only finitely many S-smooth indices
can divide their own values. -/
theorem smooth_common_divisor_bound (S : Finset ℕ) :
    0 < ∏ p ∈ S, supportCoefficient p ∧
      ∀ n m : ℕ, m ∣ n.gcd (lucasFibonacciSum n) → m.primeFactors ⊆ S →
        m ∣ ∏ p ∈ S, supportCoefficient p := by
  constructor
  · apply Finset.prod_pos
    intro p _
    unfold supportCoefficient
    split_ifs with hp
    · exact @rankCoefficient_pos p ⟨hp.ne_zero⟩
    · decide
  intro n m hm sub
  have hm0 : m≠0 := by
    rintro rfl
    have hh := (Nat.dvd_gcd_iff.mp hm)
    have hn : n=0 := by simpa using hh.1
    subst n
    exact (by decide : ¬0 ∣ lucasFibonacciSum 0) hh.2
  have prod : ∏ p ∈ m.primeFactors, p^(m.factorization p) = m := Nat.prod_factorization_pow_eq_self hm0
  calc m = ∏ p ∈ m.primeFactors, p^(m.factorization p) := prod.symm
       _ ∣ ∏ p ∈ m.primeFactors, supportCoefficient p := by
         apply Finset.prod_dvd_prod_of_dvd
         intro p hp
         obtain ⟨prime,div,_⟩ := Nat.mem_primeFactors.mp hp
         have : Fact p.Prime := ⟨prime⟩
         have high := prime.factorization_pos_of_dvd hm0 div
         obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero high.ne'
         have hcap : p^(e+1) ∣ n.gcd (lucasFibonacciSum n) := by
           simpa only [he] using (show p^(m.factorization p) ∣ n.gcd (lucasFibonacciSum n) from (Nat.ordProj_dvd m p).trans hm)
         simpa [supportCoefficient,prime,he] using
           ((attainable_index_value_power (p:=p) e).mp ⟨n,hcap⟩).2.2
       _ ∣ ∏ p ∈ S, supportCoefficient p := Finset.prod_dvd_prod_of_subset _ _ _ sub

private lemma rank_two : fibonacciStepRank 2 1=3 := by
  obtain ⟨hpos,hf⟩ := rank_properties 2 1
  have hlo := rank_min 2 1 3 (by decide) (by decide)
  generalize fibonacciStepRank 2 1 = r at *
  interval_cases r <;> revert hf <;> decide

private lemma rank_three : fibonacciStepRank 3 1=4 := by
  obtain ⟨hpos,hf⟩ := rank_properties 3 1
  have hlo := rank_min 3 1 4 (by decide) (by decide)
  generalize fibonacciStepRank 3 1 = r at *
  interval_cases r <;> revert hf <;> decide

private lemma small_coefficients : rankCoefficient 2=38 ∧ rankCoefficient 3=189 := by
  simp only [rankCoefficient_eq,rank_two,rank_three]
  decide

/-- The complete list among nontrivial prime powers consists of 3 and 27. -/
theorem prime_power_self_divides {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    p^e ∣ lucasFibonacciSum (p^e) ↔ p^e=3 ∨ p^e=27 := by
  constructor
  · intro h
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    have test := (attainable_index_value_power (p:=p) j).mp
      ⟨p^(j+1), Nat.dvd_gcd dvd_rfl h⟩
    have zero := (ZMod.natCast_eq_zero_iff ..).mpr ((dvd_pow_self _ (by omega : j+1≠0)).trans h)
    have small : p=2 ∨ p=3 := by
      rcases upper_prime_power_residues test.1 (j+1) with h4|h3
      · rw [zero] at h4
        have div : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using h4.symm)
        have lt := Nat.le_of_dvd (by decide : 0<4) div
        have lower := hp.two_le
        interval_cases p <;> revert hp div <;> decide
      · rw [zero] at h3
        have div : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using (congrArg Neg.neg h3).symm)
        exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp div)
    rcases small with rfl|rfl
    · have cap := test.2.2
      rw [small_coefficients.1] at cap
      have low : j+1 < 2 := by
        by_contra! hn
        exact (by decide : ¬2^2 ∣ 38) ((pow_dvd_pow 2 hn).trans cap)
      have : j=0 := by omega
      subst j
      exact False.elim ((by decide : ¬2 ∣ lucasFibonacciSum 2) h)
    · have cap := test.2.2
      rw [small_coefficients.2] at cap
      have low : j+1 < 4 := by
        by_contra! hn
        exact (by decide : ¬3^4 ∣ 189) ((pow_dvd_pow 3 hn).trans cap)
      have hj : j ≤ 2 := by omega
      interval_cases j <;> revert h <;> decide
  · rintro (h|h) <;> rw [h] <;> decide

#print axioms smooth_common_divisor_bound
#print axioms prime_power_self_divides

end Arxiv.«2211.10788».IndexDivisors
