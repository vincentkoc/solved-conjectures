import research.arxiv.«2211.10788».LucasFibonacciPrimePowerLifts
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Simultaneous prime-power divisors at a common prime parameter on the upper diagonal. -/

namespace Arxiv.«2211.10788»

/-- On a reduced class with sharp Fibonacci steps, prescribed extra exponents
at distinct factor primes select one reduced class of the common parameter. -/
theorem joint_lucasFibonacciSum_lift_class (S : Finset ℕ) (r d m b : ℕ → ℕ)
    {s E : ℕ} (hs : s < E) (hunit : s.Coprime E)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hsupport : ∀ p ∈ S, p ∣ E)
    (hm : ∀ p ∈ S, 0 < m p) (hp2 : ∀ p ∈ S, p*p ∣ m p)
    (hhit : ∀ p ∈ S, m p ∣ lucasFibonacciSum (r p + d p * s))
    (hf : ∀ p ∈ S, m p ∣ Nat.fib (d p * E))
    (hsharp : ∀ p ∈ S, ¬p * m p ∣ Nat.fib (d p * E)) :
    let M := E * ∏ p ∈ S, p ^ b p
    ∃ A < M, A.Coprime M ∧ ∀ n : ℕ,
      (n ≡ s [MOD E] ∧ ∀ p ∈ S, p ^ b p * m p ∣ lucasFibonacciSum (r p + d p * n)) ↔
        n ≡ A [MOD M] := by
  classical
  dsimp only
  let q (p : ℕ) := p ^ b p
  let T := ∏ p ∈ S, q p
  have single (p : ℕ) (hp : p ∈ S) : ∃ c, ∀ u : ℕ,
      q p * m p ∣ lucasFibonacciSum (r p + d p * (s + E * u)) ↔ u ≡ c [MOD q p] := by
    let : Fact p.Prime := ⟨hprime p hp⟩
    obtain ⟨c, _, hc⟩ := sharp_prime_power_lift_class (hm p hp) (hp2 p hp)
      (hhit p hp) (hf p hp) (hsharp p hp) (b p)
    refine ⟨c, fun u => ?_⟩
    simpa only [q, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc] using hc u
  let c (p : ℕ) := if hp : p ∈ S then (single p hp).choose else 0
  have hn (p : ℕ) (hp : p ∈ S) : q p ≠ 0 := pow_ne_zero _ (hprime p hp).ne_zero
  have co : Set.Pairwise (S : Set ℕ) (fun p v => (q p).Coprime (q v)) :=
    fun p hp v hv hpv => Nat.coprime_pow_primes _ _ (hprime p hp) (hprime v hv) hpv
  let C := Nat.chineseRemainderOfFinset c q S hn co
  have hC : (C : ℕ) < T := Nat.chineseRemainderOfFinset_lt_prod c q hn co
  have combine (u : ℕ) : u ≡ (C : ℕ) [MOD T] ↔ ∀ p ∈ S, u ≡ c p [MOD q p] := by
    have hlist := S.nodup_toList.pairwise_of_forall_ne (r := fun p v => (q p).Coprime (q v))
      (fun p hp v hv hne => co (Finset.mem_toList.mp hp) (Finset.mem_toList.mp hv) hne)
    have test := Nat.modEq_list_map_prod_iff (a := u) (b := (C : ℕ)) (s := q) hlist
    rw [Finset.prod_map_toList] at test
    simp only [Finset.mem_toList] at test
    exact test.trans ⟨fun h p hp => (h p hp).trans (C.prop p hp),
      fun h p hp => (h p hp).trans (C.prop p hp).symm⟩
  have cut (u : ℕ) :
      (∀ p ∈ S, q p * m p ∣ lucasFibonacciSum (r p + d p * (s + E * u))) ↔
        u ≡ (C : ℕ) [MOD T] := by
    rw [combine]
    have one (p : ℕ) (hp : p ∈ S) := (single p hp).choose_spec u
    exact forall₂_congr fun p hp => by simpa only [c, dif_pos hp] using one p hp
  have hE : 0 < E := by omega
  have hcop : (s + E * C).Coprime E := (Nat.coprime_add_mul_left_left ..).mpr hunit
  have hT : (s + E * C).Coprime T := Nat.Coprime.prod_right fun p hp =>
    (hcop.of_dvd_right (hsupport p hp)).pow_right _
  have base : s + E * C ≡ s [MOD E] := by simp [Nat.ModEq]
  refine ⟨s + E * C, ?_, hcop.mul_right hT, ?_⟩
  · have h := Nat.mul_le_mul_left E (Nat.succ_le_of_lt hC)
    rw [Nat.mul_succ] at h
    change s + E * ↑C < E * T
    omega
  · intro n
    change (_ ∧ _) ↔ n ≡ s + E * C [MOD E * T]
    have repr (h : n ≡ s [MOD E]) : n = s + E * (n / E) := by
      have hr : n % E = s := Eq.trans h (Nat.mod_eq_of_lt hs)
      rw [← hr, Nat.mod_add_div]
    constructor
    · rintro ⟨hb, h⟩
      obtain ⟨u, rfl⟩ : ∃ u, n = s + E*u := ⟨_, repr hb⟩
      exact (((cut u).mp h).mul_left' E).add_left s
    · intro h
      have hb := (h.of_dvd (dvd_mul_right E T)).trans base
      obtain ⟨u, rfl⟩ : ∃ u, n = s + E*u := ⟨_, repr hb⟩
      exact ⟨hb, (cut u).mpr ((Nat.ModEq.add_left_cancel' s h).mul_left_cancel' hE.ne')⟩


private def squareStep (p d : ℕ) (hp : p.Prime) : ℕ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  fibonacciStepRank (p ^ 2) d

private theorem squareStep_spec (p d : ℕ) (hp : p.Prime) :
    0 < squareStep p d hp ∧ p ^ 2 ∣ Nat.fib (d * squareStep p d hp) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  unfold squareStep fibonacciStepRank
  exact Nat.find_spec (p := fun t => 0 < t ∧ p ^ 2 ∣ Nat.fib (d*t)) _

/-- A common step for testing all prescribed factors. Each factor contributes
its prime and the first Fibonacci return rank modulo its square. -/
def jointPrimeIndexPeriod (S : Finset ℕ) (d : ℕ → ℕ) (hp : ∀ p ∈ S, Nat.Prime p) : ℕ :=
  ∏ x : S, x.val * squareStep x.val (d x.val) (hp x.val x.prop)

private theorem jointPeriod_spec (S : Finset ℕ) (d : ℕ → ℕ) (hp : ∀ p ∈ S, Nat.Prime p) :
    let E := jointPrimeIndexPeriod S d hp
    0 < E ∧ ∀ p ∈ S, p ∣ E ∧ p ^ 2 ∣ Nat.fib (d p * E) := by
  let f (x : S) := x.val * squareStep x.val (d x.val) (hp x.val x.prop)
  let E := ∏ x : S, f x
  change 0 < E ∧ _
  constructor
  · exact Finset.prod_pos fun x _ => Nat.mul_pos (hp x.val x.prop).pos
      (squareStep_spec x.val (d x.val) (hp x.val x.prop)).1
  · intro p h
    have hdiv : p * squareStep p (d p) (hp p h) ∣ E :=
      Finset.dvd_prod_of_mem f (Finset.mem_univ (⟨p,h⟩ : S))
    exact ⟨(dvd_mul_right ..).trans hdiv, (squareStep_spec p (d p) (hp p h)).2.trans
      (Nat.fib_dvd _ _ (Nat.mul_dvd_mul_left (d p) ((dvd_mul_left ..).trans hdiv)))⟩

/-- Arbitrarily high simultaneous powers at arbitrarily large common prime
parameters are equivalent to a finite search over the units modulo E. -/
theorem joint_prime_index_powers_iff_finite_test (S : Finset ℕ) (r d : ℕ → ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p) (hd : ∀ p ∈ S, 0 < d p) :
    let E := jointPrimeIndexPeriod S d hp
    let a := fun p => (Nat.fib (d p * E)).factorization p
    (∀ (b : ℕ → ℕ) (B : ℕ), ∃ ℓ > B, Nat.Prime ℓ ∧
      ∀ p ∈ S, p ^ b p ∣ lucasFibonacciSum (r p + d p * ℓ)) ↔
    ∃ s < E, s.Coprime E ∧ ∀ p ∈ S, p ^ a p ∣ lucasFibonacciSum (r p + d p * s) := by
  let E := jointPrimeIndexPeriod S d hp
  let a (p : ℕ) := (Nat.fib (d p * E)).factorization p
  let m (p : ℕ) := p ^ a p
  obtain ⟨hE, hstep⟩ := jointPeriod_spec S d hp
  have hpos (p : ℕ) (h : p ∈ S) : Nat.fib (d p * E) ≠ 0 :=
    (Nat.fib_pos.mpr (Nat.mul_pos (hd p h) hE)).ne'
  have hf (p : ℕ) : m p ∣ Nat.fib (d p * E) := Nat.ordProj_dvd ..
  have hp2 (p : ℕ) (h : p ∈ S) : p*p ∣ m p := by
    rw [← pow_two]
    exact pow_dvd_pow p (((hp p h).pow_dvd_iff_le_factorization (hpos p h)).mp (hstep p h).2)
  have hsharp (p : ℕ) (h : p ∈ S) : ¬p * m p ∣ Nat.fib (d p * E) := by
    simpa only [m, a, pow_succ'] using Nat.pow_succ_factorization_not_dvd (hpos p h) (hp p h)
  constructor
  · intro all
    obtain ⟨ℓ, hlt, hℓ, hh⟩ := all a E
    have hcop : ℓ.Coprime E := hℓ.coprime_iff_not_dvd.mpr fun h =>
      (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hE h)
    refine ⟨ℓ % E, Nat.mod_lt _ hE, ?_, ?_⟩
    · change (ℓ % E).gcd E = 1
      rw [← Nat.gcd_rec]
      exact hcop.symm
    · intro p h
      have hshift : m p ∣ Nat.fib ((d p * E) * (ℓ / E)) :=
        (hf p).trans (Nat.fib_dvd _ _ (dvd_mul_right ..))
      apply (lucasFibonacciSum_dvd_shift_iff (s := r p + d p * (ℓ % E)) hshift).mp
      rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.mod_add_div]
      exact hh p h
  · rintro ⟨s, hs, hu, hh⟩ b B
    obtain ⟨A, hA, hcop, hc⟩ := joint_lucasFibonacciSum_lift_class S r d m b hs hu hp
      (fun p h => (hstep p h).1) (fun p h => pow_pos (hp p h).pos _) hp2 hh
      (fun p _ => hf p) hsharp
    obtain ⟨ℓ, hB, hℓ, hl⟩ := Nat.forall_exists_prime_gt_and_modEq B (by omega) hcop
    exact ⟨ℓ, hB, hℓ, fun p h => (dvd_mul_right (p^b p) (m p)).trans (((hc ℓ).mpr hl).2 p h)⟩


private lemma prime_hits_from_sharp_unit {p s E : ℕ} (hp : p.Prime) (hs : s < E)
    (hu : s.Coprime E) (hdiv : p ∣ E) (hh : p*p ∣ lucasFibonacciSum s)
    (hf : p*p ∣ Nat.fib E) (hsharp : ¬p*(p*p) ∣ Nat.fib E) (b B : ℕ) :
    ∃ ℓ > B, Nat.Prime ℓ ∧ p^b ∣ lucasFibonacciSum ℓ := by
  obtain ⟨A, hA, hc, hclass⟩ := joint_lucasFibonacciSum_lift_class {p}
    (fun _ => 0) (fun _ => 1) (fun _ => p*p) (fun _ => b) hs hu
    (by simpa using hp) (by simpa using hdiv) (by simp [hp.pos])
    (by simp) (by simpa using hh) (by simpa using hf) (by simpa using hsharp)
  obtain ⟨ℓ, hB, hℓ, hl⟩ := Nat.forall_exists_prime_gt_and_modEq B (by omega) hc
  have hh' := ((hclass ℓ).mpr hl).2 p (Finset.mem_singleton_self p)
  exact ⟨ℓ, hB, hℓ, (dvd_mul_right (p^b) (p*p)).trans (by simpa using hh')⟩

/-- The factors 5 and 31 lift separately at arbitrarily large prime parameters,
but never divide the same upper-diagonal term, even at a composite parameter. -/
theorem five_thirty_one_separate_prime_lifts :
    (∀ p ∈ ({5, 31} : Finset ℕ), ∀ b B : ℕ, ∃ ℓ > B, Nat.Prime ℓ ∧
      p^b ∣ lucasFibonacciSum ℓ) ∧ ∀ n : ℕ, ¬155 ∣ lucasFibonacciSum n := by
  constructor
  · intro p h b B
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · apply prime_hits_from_sharp_unit (s := 17) (E := 25) <;>
        (try simp only [lucasFibonacciSum, ← Nat.fastFib_eq]) <;> decide
    · apply prime_hits_from_sharp_unit (s := 833) (E := 930) <;>
        (try simp only [lucasFibonacciSum, ← Nat.fastFib_eq]) <;> decide
  · intro n h
    have hF : 155 ∣ Nat.fib (30*(n/30)) :=
      (show 155 ∣ Nat.fib 30 by rw [← Nat.fastFib_eq]; decide).trans
        (Nat.fib_dvd _ _ (dvd_mul_right ..))
    have hred := (lucasFibonacciSum_dvd_shift_iff (s := n%30) hF).mp
    rw [Nat.mod_add_div] at hred
    have small : ∀ i : Fin 30, ¬155 ∣ lucasFibonacciSum i := by
      simp only [lucasFibonacciSum, ← Nat.fastFib_eq]
      decide
    exact small ⟨_, Nat.mod_lt n (by decide)⟩ (hred h)

#print axioms five_thirty_one_separate_prime_lifts

#print axioms joint_prime_index_powers_iff_finite_test

#print axioms joint_lucasFibonacciSum_lift_class

end Arxiv.«2211.10788»
