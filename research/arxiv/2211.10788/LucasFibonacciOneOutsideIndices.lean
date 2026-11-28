import HosoyaCofactorSupport
import HosoyaExceptionalPrimeCertificates
import HosoyaLocalCofactorTest

/-! Self-dividing upper indices with at most one prime other than two and three. -/

namespace Arxiv.«2211.10788».IndexDivisors

private lemma small_bound : smoothBound {2,3}=7182 := by
  norm_num [smoothBound,supportCoefficient,rankCoefficient_two_three.1,rankCoefficient_two_three.2]

private lemma no_six {n : ℕ} (h : n ∣ lucasFibonacciSum n) : ¬6 ∣ n := by
  intro six
  have two : 2 ∣ lucasFibonacciSum n := ((by decide : 2 ∣ 6).trans six).trans h
  have three := (by decide : 3 ∣ 6).trans six
  have := (two_dvd_upper_iff n).mp two
  omega

private lemma small_cofactor {n m : ℕ} (self : n ∣ lucasFibonacciSum n)
    (hn : n≠0) (md : m ∣ n) (sub : m.primeFactors ⊆ {2,3}) : m ∈ smallCofactors := by
  have m0 := Nat.pos_of_dvd_of_pos md (Nat.pos_of_ne_zero hn)
  have big := (smooth_common_divisor_bound {2,3}).2 n m (Nat.dvd_gcd md (md.trans self)) sub
  change m ∣ smoothBound {2,3} at big
  rw [small_bound] at big
  have cop : m.Coprime 133 := by
    apply Nat.coprime_of_dvd
    intro q prime div
    have mem := sub (prime.mem_primeFactors div m0.ne')
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl|rfl <;> decide
  have d54 : m ∣ 54 := cop.dvd_mul_right.mp (by exact big : m ∣ 54*133)
  have allowed : ∀ t ∈ (54:ℕ).divisors, ¬6 ∣ t → t ∈ smallCofactors := by decide +kernel
  exact allowed m (Nat.mem_divisors.mpr ⟨d54,by decide⟩) (fun d => no_six self (d.trans md))

private lemma possible {m p : ℕ} (hm : m ∈ smallCofactors) (hp : p.Prime)
    (h : p ∣ cofactorObstruction m) (h2 : p≠2) (h3 : p≠3) (h5 : p≠5) :
    p ∈ exceptionalPrimes := by
  have cert : ∀ t ∈ smallCofactors, (cofactorObstruction t).primeFactors ⊆
      insert 2 (insert 3 (insert 5 exceptionalPrimes)) := by decide +kernel
  have pos : 0 < m := by
    have good : ∀ t ∈ smallCofactors, 0 < t := by decide
    exact good m hm
  have mem := cert m hm (hp.mem_primeFactors h (cofactorObstruction_pos pos).ne')
  simpa [h2,h3,h5] using mem

/-- Among all indices containing at most one distinct prime outside {2,3},
the only ones dividing the canonical upper value are 1, 3 and 27. -/
theorem one_outside_two_three_self_divides (n : ℕ) (one : (n.primeFactors \ {2,3}).card≤1) :
    n ∣ lucasFibonacciSum n ↔ n=1 ∨ n=3 ∨ n=27 := by
  constructor
  · intro self
    have hn : n≠0 := by rintro rfl; exact (by decide : ¬0 ∣ lucasFibonacciSum 0) self
    by_cases smooth : n.primeFactors ⊆ {2,3}
    · have mem := small_cofactor self hn dvd_rfl smooth
      have check : ∀ m ∈ smallCofactors, m ∣ lucasFibonacciSum m → m=1 ∨ m=3 ∨ m=27 := by decide
      exact check n mem self
    obtain ⟨p,pn,out⟩ := Finset.not_subset.mp smooth
    have hp := (Nat.mem_primeFactors.mp pn).1
    have : Fact p.Prime := ⟨hp⟩
    let m := ordCompl[p] n
    let e := n.factorization p
    have decomp : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have div : p ∣ n := (Nat.mem_primeFactors.mp pn).2.1
    have hit := Nat.dvd_gcd div (div.trans self)
    have h5 := ((attainable_index_value_power (p:=p) 0).mp ⟨n,by simpa using hit⟩).1
    have co := cofactor_supported (Finset.mem_sdiff.mpr ⟨pn,out⟩) one
    have sm : m ∈ smallCofactors := small_cofactor self hn (Nat.ordCompl_dvd n p) co
    have dvd : p ∣ cofactorObstruction m := prime_dvd_cofactorObstruction h5 e
      (Nat.ordCompl_pos p hn) (by rw [decomp]; exact div.trans self)
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at out
    have ep := possible sm hp dvd out.1 out.2 h5
    have high : e < 2 := by
      by_contra! lo
      have sq : p^2 ∣ n := (pow_dvd_pow p lo).trans (Nat.ordProj_dvd n p)
      exact exceptional_no_square hp ep n (Nat.dvd_gcd sq (sq.trans self))
    have pos : 0 < e := hp.factorization_pos_of_dvd hn div
    have he : e=1 := by omega
    rw [he,pow_one] at decomp
    exact False.elim (exceptional_first_power_misses ep sm (decomp ▸ self))
  · rintro (rfl|rfl|rfl) <;> decide

#print axioms one_outside_two_three_self_divides

end Arxiv.«2211.10788».IndexDivisors
