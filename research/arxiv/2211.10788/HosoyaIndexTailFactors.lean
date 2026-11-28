import HosoyaPrimePowerCofactors

/-! Bounds for large prime divisors of an index and its upper Hosoya value. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

lemma fib_le_two_pow (n : ℕ) : Nat.fib n ≤ 2^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    simp only [Nat.fib_add_two, pow_succ] at *
    omega

/-- Distinct large prime factors consume at least h binary digits apiece. -/
lemma factor_card_weight {m e h : ℕ} (hm : 0 < m) (bound : m ≤ 2^e)
    (S : Finset ℕ) (sub : S⊆m.primeFactors) (large : ∀ p∈S, 2^h≤p) :
    h*S.card≤e := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2^(h*S.card) = ∏ _p ∈ S, (2^h : ℕ) := by simp [pow_mul]
    _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' large
    _ ≤ ∏ p ∈ m.primeFactors, p := by
      apply Finset.prod_le_prod_of_subset_of_one_le' sub
      intro p hp _
      exact (Nat.mem_primeFactors.mp hp).1.one_lt.le
    _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
    _ ≤ 2^e := bound

/-- At positive cofactor t, at most 2t+6 different prime bases can hit
the upper value at an index p*t. -/
theorem cofactor_prime_card {t : ℕ} (ht : 0 < t) :
    (cofactorObstruction t).primeFactors.card ≤ 2*t+6 := by
  let u := lucasFibonacciSum t
  have low : u≤8*Nat.fib t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    dsimp [u,lucasFibonacciSum]
    have h := Nat.fib_le_fib_succ (n:=j)
    simp only [Nat.succ_eq_add_one,Nat.fib_add_two] at *
    omega
  have high : 7*Nat.fib t-u≤8*Nat.fib t := by omega
  have cub : 8*Nat.fib t≤8*2^t := Nat.mul_le_mul_left 8 (fib_le_two_pow t)
  have b : cofactorObstruction t≤2^(2*t+6) := by
    calc
      cofactorObstruction t ≤ (8*2^t)*(8*2^t) := Nat.mul_le_mul (low.trans cub) (high.trans cub)
      _ = 2^(2*t+6) := by rw [two_mul, pow_add _ (t+t),pow_add]; ring
  simpa using factor_card_weight (h:=1) (cofactorObstruction_pos ht) b _
    (Finset.Subset.refl _) (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)

/-- When X ≤ PT, a common divisor prime greater than P leaves a cofactor at most T.
Each such cofactor permits only linearly many primes. -/
theorem very_large_prime_count (X P T : ℕ) (cut : X ≤ P*T) :
    ((Icc 1 X).filter fun n => ∃ p ∈ n.primeFactors,
      max P 5 < p ∧ p ∣ lucasFibonacciSum n).card ≤ 8*T^2 := by
  classical
  let bases (t : ℕ) := (cofactorObstruction t).primeFactors
  let choices (t : ℕ) := (bases t).image (fun p => p*t)
  have sub : ((Icc 1 X).filter fun n => ∃ p ∈ n.primeFactors,
      max P 5 < p ∧ p ∣ lucasFibonacciSum n) ⊆ (Icc 1 T).biUnion choices := by
    intro n hn
    obtain ⟨hn, p, hp, size, hit⟩ := mem_filter.mp hn
    obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    let : Fact p.Prime := ⟨pr⟩
    obtain ⟨t,rfl⟩ := dvd
    have hprod := mem_Icc.mp hn
    have tpos : 0 < t := Nat.pos_of_mul_pos_left (by omega : 0 < p*t)
    have leT : t ≤ T := by
      by_contra! h
      have := Nat.mul_lt_mul_of_pos_left h pr.pos
      have := Nat.mul_le_mul_right T ((le_max_left P 5).trans size.le)
      omega
    have hb : p ∣ cofactorObstruction t := prime_dvd_cofactorObstruction
      (by have := le_max_right P 5; omega) 1 tpos (by simpa using hit)
    exact mem_biUnion.mpr ⟨t,mem_Icc.mpr ⟨tpos,leT⟩,
      mem_image.mpr ⟨p,pr.mem_primeFactors hb (cofactorObstruction_pos tpos).ne',rfl⟩⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ t ∈ Icc 1 T, (choices t).card := card_biUnion_le
    _ ≤ ∑ _t ∈ Icc 1 T, 8*T := by
      apply sum_le_sum
      intro t ht
      obtain ⟨ht,hle⟩ := mem_Icc.mp ht
      exact (card_image_le.trans (cofactor_prime_card ht)).trans (by omega)
    _ = 8*T^2 := by simp [pow_two]; ring

#print axioms very_large_prime_count

#print axioms factor_card_weight
#print axioms cofactor_prime_card

end Arxiv.«2211.10788».IndexDivisors
