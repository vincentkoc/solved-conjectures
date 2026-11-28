import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciProgressionDivisors

/-! Prime-free intervals in arithmetic progressions on the upper Lucas–Fibonacci diagonal. -/

namespace Arxiv.«2211.10788»

open Finset

private lemma upper_strict : StrictMono lucasFibonacciSum := fun _ _ h =>
  Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono h.le)) (Nat.fib_add_two_strictMono h)

private lemma upper_le (n : ℕ) : lucasFibonacciSum n ≤ 2^(n+2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [lucas_fibonacci_sum_recurrence]
    have h : 2^(n+2) ≤ 2^(n+1+2) := Nat.pow_le_pow_right (by decide) (by omega)
    change _ ≤ 2^(n+1+2)*2
    omega

private lemma fib_le (n : ℕ) : Nat.fib n ≤ 2^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [Nat.fib_add_two, pow_succ, pow_succ]
    rw [pow_succ] at h₁
    omega

/-- One period works for every index. The Fibonacci step permutes the m² residue pairs. -/
private lemma return_period (m : ℕ) [NeZero m] :
    ∃ T : ℕ, 0 < T ∧ T ≤ m^2 ∧ ∀ s a : ℕ,
      lucasFibonacciSum (s + T*a) ≡ lucasFibonacciSum s [MOD m] := by
  let state (n : ℕ) : ZMod m × ZMod m := (Nat.fib n, Nat.fib (n+1))
  let step (v : ZMod m × ZMod m) := (v.2, v.1+v.2)
  have hinj : Function.Injective step := by
    rintro ⟨x,y⟩ ⟨z,w⟩ h
    change (y,x+y) = (w,z+w) at h
    obtain ⟨rfl,h⟩ := Prod.mk.inj h
    exact Prod.ext (add_right_cancel h) rfl
  have hs : Function.Semiconj state Nat.succ step := by
    intro n
    exact Prod.ext rfl (by simp [state, step, Nat.fib_add_two])
  let T := Function.minimalPeriod step (state 0)
  have ht := Function.isPeriodicPt_minimalPeriod step (state 0)
  refine ⟨T, Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts _), ?_, ?_⟩
  · simpa only [Fintype.card_prod, ZMod.card, pow_two] using
      Function.minimalPeriod_le_card (f := step) (x := state 0)
  · have he (n : ℕ) : state n = step^[n] (state 0) := by
      simpa [Nat.succ_iterate] using hs.iterate_right n 0
    intro s a
    have h : state (s+T*a) = state s := by
      rw [he, Function.iterate_add_apply, (ht.mul_const a).eq, ← he]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [state, lucasFibonacciSum, Nat.fib_add_two, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat] using congrArg (fun v : ZMod m × ZMod m => 2*v.1+(v.1+v.2)) h

/-- Two hits of the same prime force a Fibonacci zero at their separation. -/
private lemma common_dvd_fib {p n h : ℕ} [NeZero p] (hp : p ∣ lucasFibonacciSum n)
    (hq : p ∣ lucasFibonacciSum (n+h)) : p ∣ Nat.fib h := by
  have hr := (lucasFibonacciSum_dvd_after_hit_iff hp 1 h).mp (by simpa using hq)
  have hs : 0 < fibonacciStepRank p 1 ∧ p ∣ Nat.fib (1 * fibonacciStepRank p 1) := by
    unfold fibonacciStepRank
    generalize_proofs h
    exact Nat.find_spec h
  exact (by simpa using hs.2 : p ∣ Nat.fib (fibonacciStepRank p 1)).trans (Nat.fib_dvd _ _ hr)

/-- The repeated term factors as `a * (1 + V*l)`. The second factor is greater than one,
so it contributes a prime outside the prime factors of the prescribed modulus `V`. -/
private lemma fresh_prime {a b V u : ℕ} (hab : a ∣ b) (ha : 1 < a) (hu : a < u)
    (hmod : u ≡ a [MOD b*V]) :
    ∃ p : ℕ, p.Prime ∧ p ∣ u ∧ ¬p ∣ V ∧ a ∣ u ∧ ¬u.Prime := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_exists_eq_add hu.le).mp hmod.symm
  let c := 1 + f*j*V
  have he : u = a*c := by dsimp [c]; rw [hj, hf]; ring
  have hc : 1 < c := by
    by_contra! hz
    exact hu.not_ge (he ▸ (by simpa using Nat.mul_le_mul_left a hz))
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc.ne'
  refine ⟨p, hp, he ▸ (hpc.trans (dvd_mul_left c a)), ?_, he ▸ dvd_mul_right a c,
    he ▸ Nat.not_prime_mul ha.ne' hc.ne'⟩
  intro hpv
  exact hp.not_dvd_one ((Nat.dvd_add_iff_left (dvd_mul_of_dvd_right hpv _)).mpr hpc)

private def template (r d k : ℕ) := ∏ j ∈ range k, lucasFibonacciSum (r + d*(j+1))

private def separations (d k : ℕ) := ∏ j ∈ range k, Nat.fib (d*(j+1))

private lemma modulus_bound (r d k : ℕ) :
    (template r d k * (template r d k * k.factorial * separations d k))^2 ≤
      2^(2*(2*k*(r+d*k+2) + k*k + d*k*k)) := by
  have h₁ : template r d k ≤ (2^(r+d*k+2))^k := by
    calc
      _ ≤ ∏ _j ∈ range k, 2^(r+d*k+2) := by
        apply Finset.prod_le_prod'
        intro j hj
        have hj' := mem_range.mp hj
        exact (upper_le _).trans (Nat.pow_le_pow_right (by decide)
          (by have := Nat.mul_le_mul_left d (show j+1 ≤ k by omega); omega))
      _ = _ := by simp
  have h₂ : separations d k ≤ (2^(d*k))^k := by
    calc
      _ ≤ ∏ _j ∈ range k, 2^(d*k) := by
        apply Finset.prod_le_prod'
        intro j hj
        exact (fib_le _).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left d (mem_range.mp hj)))
      _ = _ := by simp
  have h₃ : k.factorial ≤ (2^k)^k := k.factorial_le_pow.trans
    (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le _)
  refine (Nat.pow_le_pow_left (Nat.mul_le_mul h₁ (Nat.mul_le_mul (Nat.mul_le_mul h₁ h₃) h₂)) 2).trans_eq ?_
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_mul]
  congr 1
  ring

/-- On each positive-step progression the starts of qualifying k-term blocks include a full
arithmetic progression of the stated period. Each composite term has a prime factor larger
than k that divides no other term of its block, and a second distinct prime factor. -/
theorem composite_blocks_with_separate_primes (r d k : ℕ) (hd : 0 < d) :
    ∃ T : ℕ, 0 < T ∧ T ≤ 2^(2*(2*k*(r+d*k+2) + k*k + d*k*k)) ∧
      ∀ t : ℕ, 0 < t → ∀ j < k,
        let n := r+d*(1+T*t+j)
        ¬(lucasFibonacciSum n).Prime ∧ ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ lucasFibonacciSum n ∧
          (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ lucasFibonacciSum n) ∧
          ∀ i < k, i ≠ j → ¬p ∣ lucasFibonacciSum (r+d*(1+T*t+i)) := by
  let B := template r d k
  let F := separations d k
  let V := B*k.factorial*F
  have ha (j : ℕ) : 1 < lucasFibonacciSum (r+d*(j+1)) :=
    upper_strict (show 0 < r+d*(j+1) by positivity)
  have hB : 0 < B := prod_pos (fun j _ => zero_lt_one.trans (ha j))
  have hF : 0 < F := prod_pos (fun j _ => Nat.fib_pos.mpr (by positivity))
  have hV : 0 < V := Nat.mul_pos (Nat.mul_pos hB k.factorial_pos) hF
  let : NeZero (B*V) := ⟨(Nat.mul_pos hB hV).ne'⟩
  obtain ⟨T, hT, hsize, hret⟩ := return_period (B*V)
  refine ⟨T, hT, hsize.trans (modulus_bound r d k), ?_⟩
  intro t ht j hj
  let I (i : ℕ) := r+d*(1+T*t+i)
  let a := lucasFibonacciSum (r+d*(j+1))
  have he : I j = (r+d*(j+1))+T*(d*t) := by dsimp [I]; ring
  have hg : a < lucasFibonacciSum (I j) := upper_strict (by rw [he]; exact Nat.lt_add_of_pos_right (by positivity))
  have hdvd : a ∣ B := dvd_prod_of_mem _ (mem_range.mpr hj)
  have hr : lucasFibonacciSum (I j) ≡ a [MOD B*V] := he ▸ hret _ _
  obtain ⟨p, hp, hpu, hpf, hau, hcomp⟩ := fresh_prime hdvd (ha j) hg hr
  have hfac : k.factorial ∣ V := (dvd_mul_left _ B).trans (dvd_mul_right _ F)
  have hF' : F ∣ V := dvd_mul_left _ _
  have hlarge : k < p := by
    by_contra! h
    exact hpf ((Nat.dvd_factorial hp.pos h).trans hfac)
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd (ha j).ne'
  have hqne : q ≠ p := by
    rintro rfl
    exact hpf (((hqa.trans hdvd).trans (dvd_mul_right _ k.factorial)).trans (dvd_mul_right _ F))
  refine ⟨hcomp, p, hp, hlarge, hpu, ⟨q, hq, hqne, hqa.trans hau⟩, ?_⟩
  intro i hi hij hpi
  let : NeZero p := ⟨hp.ne_zero⟩
  have exclude {u v : ℕ} (huv : u < v) (hv : v < k)
      (h₁ : p ∣ lucasFibonacciSum (I u)) (h₂ : p ∣ lucasFibonacciSum (I v)) : False := by
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt huv)
    have hev : v = u + (e+1) := by omega
    have hg' : I v = I u + d*(e+1) := by dsimp [I]; rw [hev]; ring
    have hf := common_dvd_fib h₁ (hg' ▸ h₂ : p ∣ lucasFibonacciSum (I u + d*(e+1)))
    have hdiv : Nat.fib (d*(e+1)) ∣ F := dvd_prod_of_mem _ (mem_range.mpr (by omega : e < k))
    exact hpf ((hf.trans hdiv).trans hF')
  exact (lt_or_gt_of_ne hij).elim (fun h => exclude h hj hpi hpu) (fun h => exclude h hi hpu hpi)


/-- Every dyadic interval of progression parameters contains a block of length
⌊√(log₂ N / (4r+6d+12))⌋ with the same distinct-prime witnesses. -/
theorem dyadic_composite_block (r d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    let k := Nat.sqrt (Nat.log 2 N / (4*r+6*d+12))
    ∃ s : ℕ, N ≤ s ∧ s+k ≤ 2*N ∧ ∀ j < k,
      let n := r+d*(s+j)
      ¬(lucasFibonacciSum n).Prime ∧ ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ lucasFibonacciSum n ∧
        (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ lucasFibonacciSum n) ∧
        ∀ i < k, i ≠ j → ¬p ∣ lucasFibonacciSum (r+d*(s+i)) := by
  let C := 4*r+6*d+12
  let k := Nat.sqrt (Nat.log 2 N / C)
  by_cases hk : k = 0
  · exact ⟨N, le_rfl, (by change N+k ≤ 2*N; omega), fun _ hj => by change _ < k at hj; omega⟩
  obtain ⟨T, hT, hsize, hblock⟩ := composite_blocks_with_separate_primes r d k hd
  let e := 2*(2*k*(r+d*k+2) + k*k + d*k*k)
  have hsq : C*(k*k) ≤ Nat.log 2 N :=
    (Nat.mul_le_mul_left C (Nat.sqrt_le _)).trans (Nat.mul_div_le _ _)
  have hk' : 1 ≤ k := by omega
  have hkk : k ≤ k*k := by simpa using Nat.mul_le_mul_left k hk'
  have he : e+1 ≤ C*(k*k) := by
    dsimp only [e,C]
    nlinarith only [Nat.mul_le_mul_left r hkk, hkk, hk']
  have hpow := (Nat.pow_le_pow_right (by decide : 0 < 2) (he.trans hsq)).trans
    (Nat.pow_log_le_self 2 hN.ne')
  have hlow : k ≤ e := by dsimp [e]; nlinarith [hkk]
  have hlen : k+1 ≤ 2^e := (show k+1 ≤ 2^k from Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide) hlow)
  let t := N/T+1
  have h₁ : N < T*t := Nat.lt_mul_div_succ N hT
  have h₂ : T*t ≤ N+T := by dsimp [t]; rw [Nat.mul_add_one]; exact Nat.add_le_add_right (Nat.mul_div_le N T) T
  have hwidth : T+1+k ≤ N := by
    change T ≤ 2^e at hsize
    rw [pow_succ] at hpow
    omega
  exact ⟨1+T*t, by omega, by change 1+T*t+k ≤ 2*N; omega, hblock t (Nat.zero_lt_succ _)⟩

#print axioms composite_blocks_with_separate_primes
#print axioms dyadic_composite_block

end Arxiv.«2211.10788»
