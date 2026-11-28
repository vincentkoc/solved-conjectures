import HosoyaPrimePowerIndices
import HosoyaQuadraticPowerCoefficients

/-! Local multiplicities of common prime divisors of an index and its upper Hosoya value. -/

namespace Arxiv.«2211.10788».IndexDivisors

/-- The imaginary coordinate of (3+ω) raised to the first Fibonacci return rank at p. -/
def rankCoefficient (p : ℕ) [NeZero p] : ℕ :=
  progressionPowerCoefficient 0 (fibonacciStepRank p 1)

lemma rankCoefficient_eq (p : ℕ) [NeZero p] :
    rankCoefficient p = (start^(fibonacciStepRank p 1)).im := by
  simp [rankCoefficient,progressionPowerCoefficient,start]

lemma rankCoefficient_pos (p : ℕ) [NeZero p] : 0 < rankCoefficient p := by
  rw [rankCoefficient_eq]
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (rank_properties p 1).1.ne'
  rw [hj]
  clear hj
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ,QuadraticAlgebra.im_mul]
    change 0<(start^(j+1)).im at ih
    change 0 < _ * 1 + (start^(_+1)).im*3 + 1*(start^(_+1)).im*1
    omega

private lemma unit_re {p : ℕ} (hp : p.Prime) (z : Q) (h : z.re.Coprime z.im)
    (hi : p ∣ z.im) : ¬p ∣ z.re := by
  intro hr
  exact hp.not_dvd_one (h ▸ Nat.dvd_gcd hr hi)

private lemma shifted_scalar {p : ℕ} [Fact p.Prime] {e n : ℕ} (hn : p^e ∣ n) :
    let R := fibonacciStepRank p 1
    p^(e+1) ∣ (w^(n*R)).im := by
  let R := fibonacciStepRank p 1
  have hF : p ∣ (w^R).im := by simpa [R,fib_coord] using (rank_properties p 1).2
  obtain ⟨t,rfl⟩ := hn
  change p^(e+1) ∣ (w^(p^e*t*R)).im
  rw [show p^e*t*R=R*p^e*t by ring,pow_mul,pow_mul]
  exact (wild_power Fact.out (w^R) hF e).trans (im_dvd_power _ t)

/-- On indices divisible by p^e, lifting a hit from p to p^(e+1) depends only
on a single fixed integer attached to p. This also covers e=0 and p=2. -/
theorem upper_divisor_on_tower {p : ℕ} [Fact p.Prime] (h5 : p≠5) {n e : ℕ}
    (hn : p^e ∣ n) :
    p^(e+1) ∣ lucasFibonacciSum n ↔
      p ∣ lucasFibonacciSum n ∧ p^(e+1) ∣ rankCoefficient p := by
  let R := fibonacciStepRank p 1
  let z := start*w^n
  let u := w^(n*R)
  have hp : p.Prime := Fact.out
  have pp : p ∣ p^(e+1) := dvd_pow_self _ (by omega)
  have hi : p^(e+1) ∣ u.im := shifted_scalar hn
  have gu : u.re.Coprime u.im := by simpa [u] using primitive_shift 1 (by decide) (n*R)
  have c : (p^(e+1)).Coprime u.re :=
    (hp.coprime_iff_not_dvd.mpr (unit_re hp _ gu (pp.trans hi))).pow_left _
  have gz := primitive_shift start (by decide) n
  have hprod : z^R=start^R*u := by dsimp [z,u]; rw [mul_pow,pow_mul]
  have hc : p^(e+1) ∣ (z^R).im ↔ p^(e+1) ∣ rankCoefficient p := by
    rw [hprod,rankCoefficient_eq]
    exact scalar_product _ _ hi c
  rw [←upper_coeff]
  change p^(e+1) ∣ z.im ↔ p ∣ z.im ∧ _
  by_cases hit : p ∣ z.im
  · rw [and_iff_right hit,←hc]
    exact (tame_power hp z hit (unit_re hp z gz hit) (rank_tame h5) _).symm
  · simp only [hit,false_and,iff_false]
    exact fun hh => hit (pp.trans hh)

/-- Exact attainable powers in gcd(n,U(n)). The ramified prime five and the
norm prime eleven never occur. At every other prime the rank coefficient
determines the whole range, including its largest exponent. -/
theorem attainable_index_value_power {p : ℕ} [Fact p.Prime] (e : ℕ) :
    (∃ n : ℕ, p^(e+1) ∣ n.gcd (lucasFibonacciSum n)) ↔
      p≠5 ∧ p≠11 ∧ p^(e+1) ∣ rankCoefficient p := by
  have pp : p ∣ p^(e+1) := dvd_pow_self _ (by omega)
  have prev : p^e ∣ p^(e+1) := pow_dvd_pow _ (by omega)
  constructor
  · rintro ⟨n,h⟩
    obtain ⟨hn,hu⟩ := Nat.dvd_gcd_iff.mp h
    obtain ⟨t,ht⟩ := hn
    have hn : p^(e+1) ∣ n := ⟨t,ht⟩
    have hit : ∃ t, p ∣ lucasFibonacciSum (0+p^(e+1)*t) := ⟨t,by simpa [←ht] using pp.trans hu⟩
    have htest := (prime_dvd_lucasFibonacciSum_on_progression_iff 0 (p^(e+1))).mp hit
    split_ifs at htest with h5
    · subst p
      simp [pp] at htest
    · exact ⟨h5,htest.1,((upper_divisor_on_tower h5 (prev.trans hn)).mp hu).2⟩
  · rintro ⟨h5,h11,hc⟩
    have hit : ∃ t, p ∣ lucasFibonacciSum (0+p^(e+1)*t) := by
      apply (prime_dvd_lucasFibonacciSum_on_progression_iff _ _).mpr
      rw [if_neg h5,rank_prime_power_step h5]
      exact ⟨h11,pp.trans hc⟩
    obtain ⟨t,ht⟩ := hit
    let n := p^(e+1)*t
    have hn : p^(e+1) ∣ n := dvd_mul_right ..
    exact ⟨n,Nat.dvd_gcd hn ((upper_divisor_on_tower h5 (prev.trans hn)).mpr
      ⟨by simpa [n] using ht,hc⟩)⟩

#print axioms rankCoefficient_pos
#print axioms upper_divisor_on_tower
#print axioms attainable_index_value_power

end Arxiv.«2211.10788».IndexDivisors
