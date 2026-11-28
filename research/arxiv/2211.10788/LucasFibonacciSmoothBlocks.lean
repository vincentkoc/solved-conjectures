import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes
import research.arxiv.«2211.10788».LucasFibonacciProgressionDivisors

/-! Counting terms of the upper Lucas–Fibonacci diagonal supported on a finite set of primes. -/

namespace Arxiv.«2211.10788»

open Finset

private lemma term_growth (n : ℕ) : 2^n ≤ (lucasFibonacciSum n)^2 := by
  have hmono : Monotone lucasFibonacciSum := fun i j hij => by
    unfold lucasFibonacciSum
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.fib_mono hij))
      (Nat.fib_mono (Nat.add_le_add_right hij _))
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h _ =>
    rw [pow_add, lucas_fibonacci_sum_recurrence]
    have hh := hmono (Nat.le_succ n)
    nlinarith [Nat.mul_le_mul hh hh, Nat.mul_le_mul_right (lucasFibonacciSum n) hh]

private lemma fib_upper (n : ℕ) : Nat.fib n ≤ 2^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    rw [Nat.fib_add_two, pow_succ, pow_succ]
    rw [pow_succ] at h1
    omega

private lemma common_factor_dvd_fib {m i j : ℕ} [NeZero m]
    (h₁ : m ∣ lucasFibonacciSum i) (h₂ : m ∣ lucasFibonacciSum (i+j)) :
    m ∣ Nat.fib j := by
  have hr : fibonacciStepRank m 1 ∣ j :=
    (lucasFibonacciSum_dvd_after_hit_iff h₁ 1 j).mp (by simpa using h₂)
  have hs : 0 < fibonacciStepRank m 1 ∧ m ∣ Nat.fib (1 * fibonacciStepRank m 1) := by
    unfold fibonacciStepRank
    generalize_proofs h
    exact Nat.find_spec h
  exact (by simpa using hs.2 : m ∣ Nat.fib (fibonacciStepRank m 1)).trans (Nat.fib_dvd _ _ hr)

private lemma largest_prime_power (P : Finset ℕ) {a : ℕ} (ha : 1 < a)
    (hp : a.primeFactors ⊆ P) :
    ∃ p ∈ P, p.Prime ∧ a ≤ (p ^ a.factorization p)^P.card := by
  obtain ⟨p, hmem, hmax⟩ := exists_max_image a.primeFactors
    (fun q => q ^ a.factorization q) (Nat.nonempty_primeFactors.mpr ha)
  have hprime := Nat.prime_of_mem_primeFactors hmem
  refine ⟨p, hp hmem, hprime, ?_⟩
  calc
    a = _ := Nat.prod_primeFactors_pow_factorization (by omega)
    _ ≤ ∏ _q ∈ a.primeFactors, p ^ a.factorization p := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun q hq => hmax q hq)
    _ = (p ^ a.factorization p)^a.primeFactors.card := prod_const _
    _ ≤ _ := Nat.pow_le_pow_right (Nat.pow_pos hprime.pos) (card_le_card hp)

private lemma dominant_gap (r d N R p a b : ℕ) (hd : 0 < d) (ha : N ≤ a) (hab : a < b)
    (hp : p.Prime)
    (h₁ : lucasFibonacciSum (r+d*a) ≤ (p^(lucasFibonacciSum (r+d*a)).factorization p)^R)
    (h₂ : lucasFibonacciSum (r+d*b) ≤ (p^(lucasFibonacciSum (r+d*b)).factorization p)^R) :
    N ≤ (b-a)*(2*R) := by
  let u := lucasFibonacciSum (r+d*a)
  let v := lucasFibonacciSum (r+d*b)
  let e := min (u.factorization p) (v.factorization p)
  let m := p^e
  have hm : 0 < m := Nat.pow_pos hp.pos
  let : NeZero m := ⟨hm.ne'⟩
  have hdu : m ∣ u := (pow_dvd_pow p (min_le_left ..)).trans (Nat.ordProj_dvd u p)
  have hdv : m ∣ v := (pow_dvd_pow p (min_le_right ..)).trans (Nat.ordProj_dvd v p)
  have hdiff : r+d*a+d*(b-a) = r+d*b := by rw [Nat.add_assoc, ← Nat.mul_add, show a+(b-a)=b by omega]
  have hf : m ∣ Nat.fib (d*(b-a)) := common_factor_dvd_fib hdu (by simpa [hdiff] using hdv)
  have hupper := (Nat.le_of_dvd (Nat.fib_pos.mpr (Nat.mul_pos hd (Nat.sub_pos_of_lt hab))) hf).trans
    (fib_upper (d*(b-a)))
  have hlower : 2^(d*N) ≤ (m^R)^2 := by
    rcases le_total (u.factorization p) (v.factorization p) with h | h
    · have he : m = p^u.factorization p := by simp [m, e, min_eq_left h]
      rw [he]
      exact (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_le_mul_left d ha] : d*N ≤ r+d*a)).trans
        ((term_growth _).trans (Nat.pow_le_pow_left h₁ 2))
    · have he : m = p^v.factorization p := by simp [m, e, min_eq_right h]
      rw [he]
      exact (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_le_mul_left d (ha.trans hab.le)] : d*N ≤ r+d*b)).trans
        ((term_growth _).trans (Nat.pow_le_pow_left h₂ 2))
  have hh := hlower.trans (Nat.pow_le_pow_left (Nat.pow_le_pow_left hupper R) 2)
  rw [← pow_mul, ← pow_mul] at hh
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  exact Nat.le_of_mul_le_mul_left (show d*N ≤ d*((b-a)*(2*R)) by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using he) hd

/-- The number of terms supported on a specified finite set of primes, in a
dyadic block of any positive-step index progression, is at most twice the
square of the size of the set. -/
theorem smooth_block_card_le (P : Finset ℕ) (r d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    ((Ico N (2*N)).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P).card ≤
      2 * P.card^2 := by
  classical
  let A := (Ico N (2*N)).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P
  let u (t : ℕ) := lucasFibonacciSum (r+d*t)
  let R := P.card
  have index {t : ℕ} (ht : t ∈ A) : N ≤ t ∧ t < 2*N := mem_Ico.mp (mem_filter.mp ht).1
  have choosePrime (t : A) : ∃ p ∈ P, p.Prime ∧ u t ≤ (p^(u t).factorization p)^R := by
    have ht := index t.2
    have hn : 0 < r+d*(t : ℕ) := by have := Nat.mul_pos hd (hN.trans_le ht.1); omega
    have hh := term_growth (r+d*(t : ℕ))
    have hpow : 1 < (2 : ℕ)^(r+d*(t : ℕ)) := one_lt_pow₀ (by decide) hn.ne'
    have hu : 1 < u t := by change 2^_ ≤ (u t)^2 at hh; nlinarith
    exact largest_prime_power P hu (mem_filter.mp t.2).2
  choose prime hmem hprime hmax using choosePrime
  let bucket (t : ℕ) := (2*R*t)/N
  let f (t : A) := (prime t, bucket t)
  have hmaps (t : A) : f t ∈ P ×ˢ Ico (2*R) (4*R) := by
    have hh := index t.2
    apply mem_product.mpr
    refine ⟨hmem t, mem_Ico.mpr ⟨(Nat.le_div_iff_mul_le hN).mpr (Nat.mul_le_mul_left (2*R) hh.1),
      (Nat.div_lt_iff_lt_mul hN).mpr ?_⟩⟩
    have hr : 0 < R := card_pos.mpr ⟨prime t, hmem t⟩
    have h := Nat.mul_lt_mul_of_pos_left hh.2 (by omega : 0 < 2*R)
    nlinarith
  have distinct (a b : A) (hab : (a : ℕ) < b) (hf : f a = f b) : False := by
    obtain ⟨hp, hb⟩ := Prod.mk.inj hf
    have hh := dominant_gap r d N R (prime a) a b hd (index a.2).1 hab (hprime a)
      (hmax a) (hp ▸ hmax b)
    have hlow := Nat.div_mul_le_self (2*R*(a : ℕ)) N
    have hhigh := Nat.lt_div_mul_add (a := 2*R*(b : ℕ)) hN
    change 2*R*(a : ℕ)/N = 2*R*(b : ℕ)/N at hb
    rw [← hb] at hhigh
    have hsub := Nat.sub_add_cancel hab.le
    nlinarith [congrArg (fun x : ℕ => 2*R*x) hsub]
  have hinj : Function.Injective f := by
    intro a b h
    rcases lt_trichotomy (a : ℕ) (b : ℕ) with hlt|he|hgt
    · exact (distinct a b hlt h).elim
    · exact Subtype.ext he
    · exact (distinct b a hgt h.symm).elim
  have hcard := card_le_card_of_injOn f (s := (univ : Finset A))
    (t := P ×ˢ Ico (2*R) (4*R)) (fun t _ => hmaps t) hinj.injOn
  have hdiff : 4*R - 2*R = 2*R := by omega
  simp only [card_univ, Fintype.card_coe, card_product, Nat.card_Ico, hdiff] at hcard
  change A.card ≤ 2*R^2
  exact hcard.trans_eq (by change R*(2*R)=2*R^2; ring)

/-- Any finite list of primes containing all prime factors occurring in a
dyadic index block must contain at least `√(N/2)` elements. -/
theorem distinct_factors_in_block (r d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    N ≤ 2 * ((Ico N (2*N)).biUnion fun t => (lucasFibonacciSum (r+d*t)).primeFactors).card^2 := by
  let I := Ico N (2*N)
  let P := I.biUnion fun t => (lucasFibonacciSum (r+d*t)).primeFactors
  have h := smooth_block_card_le P r d N hd hN
  have hfull (t : ℕ) (ht : t ∈ I) : (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P :=
    fun p hp => mem_biUnion.mpr ⟨t, ht, hp⟩
  change (I.filter _).card ≤ _ at h
  rwa [filter_true_of_mem hfull, Nat.card_Ico, show 2*N-N=N by omega] at h

private lemma smooth_prefix_bound (P : Finset ℕ) (r d N : ℕ) (hd : 0 < d) :
    ((range N).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P).card ≤
      1 + 2*P.card^2*(Nat.log 2 N + 1) := by
  let cond (t : ℕ) := (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P
  have blocks (j : ℕ) : ((range (2^j)).filter cond).card ≤ 1 + 2*P.card^2*j := by
    induction j with
    | zero => simpa using (card_filter_le (range 1) cond)
    | succ j ih =>
      have hN : 0 < 2^j := by positivity
      have h := smooth_block_card_le P r d (2^j) hd hN
      have hcard : ((range (2^(j+1))).filter cond).card =
          ((range (2^j)).filter cond).card + ((Ico (2^j) (2*2^j)).filter cond).card := by
        simp only [card_eq_sum_ones, sum_filter, pow_succ']
        change (∑ t ∈ range (2*2^j), if cond t then 1 else (0 : ℕ)) = _
        exact (sum_range_add_sum_Ico _ (by omega)).symm
      rw [hcard, Nat.mul_succ]
      change ((Ico _ _).filter cond).card ≤ _ at h
      omega
  exact (card_le_card (filter_subset_filter _ (range_mono
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le))).trans (blocks _)

private lemma prime_counting_over_log {x : ℝ} (hx : 1 < x)
    (h : (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ) ≤ (Real.log 4 + 1) *
      Real.sqrt x / Real.log (Real.sqrt x)) :
    (Nat.primeCounting ⌊Real.sqrt x⌋₊ : ℝ)^2 ≤
      (2 * (Real.log 4 + 1))^2 * x / (Real.log x)^2 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.log_sqrt hx0.le] at h
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
  calc
    _ ≤ _ := hsq
    _ = _ := by field_simp; nlinarith [Real.sq_sqrt hx0.le]

open Filter
open scoped Topology

/-- On every positive-step progression, the indices at which all prime factors
are at most the square root of the actual sequence index have natural density zero. -/
theorem sqrt_smooth_density_zero (r d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (((range N).filter fun t =>
      ∀ p ∈ (lucasFibonacciSum (r+d*t)).primeFactors, p^2 ≤ r+d*t).card : ℝ) / N)
      atTop (𝓝 0) := by
  let K := r+d+1
  let C : ℝ := (2*(Real.log 4+1))^2
  have hK : (0 : ℝ) < K := by dsimp [K]; positivity
  have hKN : Tendsto (fun N : ℕ => (K : ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hK
  have hs := (Real.tendsto_sqrt_atTop.comp hKN).eventually (Chebyshev.eventually_primeCounting_le
    (by norm_num : (0 : ℝ) < 1))
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let c : ℝ := 2*C*K*(1/Real.log 2+1)
  have lim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ + c * (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).add
      ((tendsto_inv_atTop_zero.comp hlogN).const_mul c)
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ lim
  filter_upwards [hs, eventually_ge_atTop 2, hlogN.eventually_ge_atTop 1] with N hπ hN hlog
  let y := Nat.sqrt (K*N)
  let P := y.primesLE
  have hx : (1 : ℝ) < (K : ℝ)*N := by
    exact_mod_cast (show 1 < K*N by have := Nat.mul_le_mul_right N (show 1 ≤ K by dsimp [K]; omega); omega)
  have hy : y = ⌊Real.sqrt ((K : ℝ)*N)⌋₊ := by
    simp [y, ← Nat.cast_mul, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  have hprime := prime_counting_over_log hx hπ
  have hKlog : Real.log (N : ℝ) ≤ Real.log ((K : ℝ)*N) := by
    apply Real.log_le_log (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) N, show (1 : ℝ) ≤ K by exact_mod_cast (by dsimp [K]; omega : 1 ≤ K)]
  have hP : (P.card : ℝ)^2 ≤ C * (K*N) / (Real.log N)^2 := by
    change ((y.primesLE.card : ℕ) : ℝ)^2 ≤ _
    rw [Nat.primesLE_card_eq_primeCounting, hy]
    exact hprime.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr))
  have hsub : ((range N).filter fun t =>
      ∀ p ∈ (lucasFibonacciSum (r+d*t)).primeFactors, p^2 ≤ r+d*t) ⊆
      (range N).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P := by
    intro t ht
    obtain ⟨ht, hsmall⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨ht, fun p hp => ?_⟩
    have hr : r ≤ r*N := by simpa using Nat.mul_le_mul_left r (by omega : 1 ≤ N)
    have hdN := Nat.mul_le_mul_left d (mem_range.mp ht).le
    have hidx : r+d*t ≤ K*N := by dsimp [K]; nlinarith
    exact Nat.mem_primesLE.mpr ⟨Nat.le_sqrt'.mpr ((hsmall p hp).trans hidx),
      Nat.prime_of_mem_primeFactors hp⟩
  have Hnat := (card_le_card hsub).trans (smooth_prefix_bound P r d N hd)
  have hR : (((range N).filter fun t => ∀ p ∈ (lucasFibonacciSum (r+d*t)).primeFactors,
      p^2 ≤ r+d*t).card : ℝ) ≤ 1+2*(P.card : ℝ)^2*(Nat.log 2 N+1 : ℝ) := by exact_mod_cast Hnat
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : (Nat.log 2 N+1 : ℝ) ≤ Real.log N*(1/Real.log 2+1) := by
    have hn := Real.natLog_le_logb N 2
    rw [Real.logb] at hn
    push_cast at hn
    linarith [show Real.log N * (1/Real.log 2) = Real.log N / Real.log 2 by ring]
  have hup := mul_le_mul hP hlogs (by positivity) (by positivity : 0 ≤ C*(K*N)/(Real.log N)^2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply (div_le_iff₀ hN0).mpr
  have heq : 1 + 2*(C*(K*N)/(Real.log N)^2)*(Real.log N*(1/Real.log 2+1)) =
      ((N : ℝ)⁻¹ + c*(Real.log N)⁻¹)*N := by
    dsimp [c]
    field_simp [hN0.ne', (by linarith : Real.log N ≠ 0), hl2.ne']
  rw [← heq]
  linarith

#print axioms smooth_block_card_le
#print axioms distinct_factors_in_block
#print axioms sqrt_smooth_density_zero

end Arxiv.«2211.10788»
