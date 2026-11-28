import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciSmoothBlocks

/-!
# Large prime factors on Lucas–Fibonacci index progressions

A prime power shared by two terms divides the Fibonacci number at their
index difference. Comparing every valuation with its largest occurrence
in a short interval controls the product of the terms by their lcm.
-/

namespace Arxiv.«2211.10788»
open Finset

private lemma sum_along_injection (A J : Finset ℕ) (w v h : ℕ → ℕ)
    (hmap : ∀ i ∈ A, h i ∈ J) (hinj : Set.InjOn h A)
    (hle : ∀ i ∈ A, w i ≤ v (h i)) :
    (∑ i ∈ A, w i) ≤ ∑ j ∈ J, v j := by
  calc
    _ ≤ ∑ i ∈ A, v (h i) := sum_le_sum hle
    _ = ∑ j ∈ A.image h, v j := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by intro j hj; obtain ⟨i,hi,rfl⟩ := mem_image.mp hj; exact hmap i hi) (by simp)

private lemma gap_valuation (r d p a b : ℕ) (hd : 0 < d) (hp : p.Prime) (hab : a < b) :
    min ((lucasFibonacciSum (r+d*a)).factorization p)
      ((lucasFibonacciSum (r+d*b)).factorization p) ≤ (Nat.fib (d*(b-a))).factorization p := by
  let u := lucasFibonacciSum (r+d*a)
  let v := lucasFibonacciSum (r+d*b)
  let e := min (u.factorization p) (v.factorization p)
  let m := p^e
  have : NeZero m := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hu : m ∣ u := (pow_dvd_pow p (min_le_left ..)).trans (Nat.ordProj_dvd u p)
  have hv : m ∣ v := (pow_dvd_pow p (min_le_right ..)).trans (Nat.ordProj_dvd v p)
  have he : r+d*a+d*(b-a) = r+d*b := by rw [Nat.add_assoc,←Nat.mul_add,show a+(b-a)=b by omega]
  exact (hp.pow_dvd_iff_le_factorization (Nat.fib_pos.mpr (Nat.mul_pos hd (by omega))).ne').mp
    (common_divisor_lucasFibonacciSum_dvd_fib hu (by simpa [he] using hv))

private lemma interval_valuation (T : Finset ℕ) (r d a L p : ℕ) (hd : 0 < d) (hp : p.Prime)
    (hT : T ⊆ Ico a (a+L)) {s : ℕ} (hs : s ∈ T)
    (hm : ∀ t ∈ T, (lucasFibonacciSum (r+d*t)).factorization p ≤
      (lucasFibonacciSum (r+d*s)).factorization p) :
    (∑ t ∈ T, (lucasFibonacciSum (r+d*t)).factorization p) ≤
      (lucasFibonacciSum (r+d*s)).factorization p +
        2*∑ j ∈ Icc 1 L, (Nat.fib (d*j)).factorization p := by
  let w (t : ℕ) := (lucasFibonacciSum (r+d*t)).factorization p
  let v (j : ℕ) := (Nat.fib (d*j)).factorization p
  let S := T.erase s
  have si := mem_Ico.mp (hT hs)
  have left : (∑ t ∈ S.filter (· < s), w t) ≤ ∑ j ∈ Icc 1 L, v j := by
    apply sum_along_injection _ _ _ _ (s - ·)
    · intro t ht
      obtain ⟨ht,hlt⟩ := mem_filter.mp ht
      have ht' := mem_Ico.mp (hT (mem_of_mem_erase ht))
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro x hx y hy e
      have := (mem_filter.mp hx).2
      have := (mem_filter.mp hy).2
      dsimp at e; omega
    · intro t ht
      obtain ⟨ht,hlt⟩ := mem_filter.mp ht
      have h := gap_valuation r d p t s hd hp hlt
      rwa [min_eq_left (hm t (mem_of_mem_erase ht))] at h
  have right : (∑ t ∈ S.filter (fun t => ¬t<s), w t) ≤ ∑ j ∈ Icc 1 L, v j := by
    apply sum_along_injection _ _ _ _ (· - s)
    · intro t ht
      obtain ⟨ht,hlt⟩ := mem_filter.mp ht
      obtain ⟨hne,ht'⟩ := mem_erase.mp ht
      have := mem_Ico.mp (hT ht')
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro x hx y hy e
      have := (mem_filter.mp hx).2
      have := (mem_filter.mp hy).2
      dsimp at e; omega
    · intro t ht
      obtain ⟨ht,hlt⟩ := mem_filter.mp ht
      obtain ⟨hne,ht'⟩ := mem_erase.mp ht
      have h := gap_valuation r d p s t hd hp (by omega)
      rwa [min_eq_right (hm t ht')] at h
  have hsplit := S.sum_filter_add_sum_filter_not (fun t => t<s) w
  have herase := T.add_sum_erase w hs
  change w s + ∑ t ∈ S, w t = _ at herase
  change (∑ t ∈ T, w t) ≤ w s + 2*∑ j ∈ Icc 1 L, v j
  omega

private lemma term_pos (n : ℕ) : 0 < lucasFibonacciSum n := by
  have h := Nat.fib_pos.mpr (show 0 < n+2 by omega)
  unfold lucasFibonacciSum; omega

/-- Short-interval product bound. The square accounts for the two directions
from a term of maximal valuation for each prime. -/
theorem lucasFibonacciSum_prod_dvd_lcm_mul_fib (T : Finset ℕ) (r d a L : ℕ) (hd : 0 < d)
    (hT : T ⊆ Ico a (a+L)) :
    (∏ t ∈ T, lucasFibonacciSum (r+d*t)) ∣
      T.lcm (fun t => lucasFibonacciSum (r+d*t)) * (∏ j ∈ Icc 1 L, Nat.fib (d*j))^2 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl|hne
  · simp
  let u (t : ℕ) := lucasFibonacciSum (r+d*t)
  let F (j : ℕ) := Nat.fib (d*j)
  have hu (t : ℕ) : u t ≠ 0 := (term_pos _).ne'
  have hF (j : ℕ) (hj : j ∈ Icc 1 L) : F j ≠ 0 :=
    (Nat.fib_pos.mpr (Nat.mul_pos hd (mem_Icc.mp hj).1)).ne'
  have hl : T.lcm u ≠ 0 := lcm_ne_zero_iff.mpr (fun t _ => hu t)
  have hf : (∏ j ∈ Icc 1 L, F j) ≠ 0 := prod_ne_zero_iff.mpr hF
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr (fun t _ => hu t))
    (mul_ne_zero hl (pow_ne_zero _ hf))).mp
  intro p
  by_cases hp : p.Prime
  · obtain ⟨s,hs,hm⟩ := exists_max_image T (fun t => (u t).factorization p) hne
    have hi := interval_valuation T r d a L p hd hp hT hs hm
    have hs' := (Nat.factorization_le_iff_dvd (hu s) hl).mpr (dvd_lcm hs) p
    change (T.prod u).factorization p ≤ (T.lcm u * (∏ j ∈ Icc 1 L, F j)^2).factorization p
    rw [Nat.factorization_mul hl (pow_ne_zero _ hf),Finsupp.add_apply,Nat.factorization_pow,
      Finsupp.smul_apply,smul_eq_mul,Nat.factorization_prod_apply (fun t _ => hu t),
      Nat.factorization_prod_apply hF]
    change (∑ t ∈ T, (u t).factorization p) ≤ (u s).factorization p +
      2*∑ j ∈ Icc 1 L, (F j).factorization p at hi
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]


private lemma lcm_le_of_support {T P : Finset ℕ} (u : ℕ → ℕ) (M : ℕ)
    (hu : ∀ t ∈ T, 0 < u t) (hm : ∀ t ∈ T, u t ≤ M)
    (hs : ∀ t ∈ T, (u t).primeFactors ⊆ P) (hM : 0 < M) : T.lcm u ≤ M^P.card := by
  classical
  rcases T.eq_empty_or_nonempty with rfl|hne
  · simpa using (show 1 ≤ M^P.card from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hM.ne'))
  choose a ha hmax using (fun p : ℕ => exists_max_image T (fun t => (u t).factorization p) hne)
  let q (p : ℕ) := p^(u (a p)).factorization p
  have hq (p : ℕ) : 0 < q p := by
    by_cases h : p = 0
    · simp [q,h]
    · exact pow_pos (Nat.pos_of_ne_zero h) _
  have hdiv : T.lcm u ∣ P.prod q := by
    apply Finset.lcm_dvd
    intro t ht
    have he : (∏ p ∈ P, p^(u t).factorization p) = u t := by
      refine Eq.trans ?_ (Nat.prod_primeFactors_pow_factorization (hu t ht).ne').symm
      apply (prod_subset (hs t ht) ?_).symm
      intro p _ hp
      have h0 : (u t).factorization p = 0 := by
        exact Finsupp.notMem_support_iff.mp hp
      simp [h0]
    rw [←he]
    exact prod_dvd_prod_of_dvd _ _ (fun p _ => pow_dvd_pow p (hmax p t ht))
  calc
    _ ≤ P.prod q := Nat.le_of_dvd (prod_pos (fun p _ => hq p)) hdiv
    _ ≤ ∏ _p ∈ P, M := prod_le_prod' (fun p _ =>
      (Nat.le_of_dvd (hu _ (ha p)) (Nat.ordProj_dvd _ p)).trans (hm _ (ha p)))
    _ = _ := by simp

private lemma term_upper (n : ℕ) : lucasFibonacciSum n ≤ 2^(n+3) := by
  have h := fib_le_two_pow n
  have h' := fib_le_two_pow (n+2)
  rw [pow_add] at h' ⊢
  unfold lucasFibonacciSum; omega

/-- A short-interval bound for terms supported on an arbitrary set of primes.
The interval length controls the cost of repeated occurrences of a prime. -/
theorem lucasFibonacciSum_smooth_interval_bound (T P : Finset ℕ) (r d a L : ℕ) (hd : 0 < d)
    (hT : T ⊆ Ico a (a+L)) (hs : ∀ t ∈ T, (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P) :
    d*a*T.card ≤ 2*(r+d*(a+L)+3)*P.card + 4*d*L^2 := by
  let u (t : ℕ) := lucasFibonacciSum (r+d*t)
  let F (j : ℕ) := Nat.fib (d*j)
  let E := r+d*(a+L)+3
  have hmin (t : ℕ) (ht : t ∈ T) : 2^(d*a) ≤ (u t)^2 :=
    (Nat.pow_le_pow_right (by decide) (show d*a ≤ r+d*t by
      have := Nat.mul_le_mul_left d (mem_Ico.mp (hT ht)).1; omega)).trans (two_pow_le_lucasFibonacciSum_sq _)
  have hlower : 2^(d*a*T.card) ≤ (T.prod u)^2 := by
    simpa only [prod_const,←pow_mul,prod_pow] using prod_le_prod' hmin
  have hmax (t : ℕ) (ht : t ∈ T) : u t ≤ 2^E := by
    refine (term_upper _).trans (Nat.pow_le_pow_right (by decide) ?_)
    have := Nat.mul_le_mul_left d (mem_Ico.mp (hT ht)).2.le
    dsimp [E]; omega
  have hl := lcm_le_of_support u _ (fun t _ => term_pos _) hmax hs (pow_pos (by decide) _)
  have hF (j : ℕ) (hj : j ∈ Icc 1 L) : F j ≤ 2^(d*L) :=
    (fib_le_two_pow _).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left d (mem_Icc.mp hj).2))
  have hfp : (Icc 1 L).prod F ≤ 2^(d*L*L) := by
    simpa only [prod_const,Nat.card_Icc,Nat.add_sub_cancel,←pow_mul] using prod_le_prod' hF
  have hfpos : 0 < (Icc 1 L).prod F := prod_pos (fun j hj => Nat.fib_pos.mpr (Nat.mul_pos hd (mem_Icc.mp hj).1))
  have hlpos : 0 < T.lcm u := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun t _ => (term_pos _).ne')
  have hu := Nat.le_of_dvd (Nat.mul_pos hlpos (pow_pos hfpos 2)) (lucasFibonacciSum_prod_dvd_lcm_mul_fib T r d a L hd hT)
  have h := hlower.trans (Nat.pow_le_pow_left (hu.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_left hfp 2))) 2)
  rw [←pow_mul,←pow_mul,←pow_add,←pow_mul] at h
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h
  dsimp [E] at he
  nlinarith only [he]


private lemma tiled_smooth_count (P : Finset ℕ) (r d K B : ℕ)
    (hd : 0 < d) (hK : 0 < K) (hB : r+3 ≤ B) :
    ((range (K^2*B)).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P).card ≤
      5*K*B + 4*K^3*P.card := by
  classical
  let S (j : ℕ) := (Ico (j*B) (j*B+B)).filter fun t =>
    (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P
  let J := Ico K (K^2)
  have hpart : ((range (K^2*B)).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P) ⊆
      range (K*B) ∪ J.biUnion S := by
    intro t ht
    obtain ⟨ht,hp⟩ := mem_filter.mp ht
    have ht' := mem_range.mp ht
    by_cases hsmall : t < K*B
    · exact mem_union_left _ (mem_range.mpr hsmall)
    · apply mem_union_right
      refine mem_biUnion.mpr ⟨t/B, mem_Ico.mpr ⟨(Nat.le_div_iff_mul_le (by omega)).mpr (by omega),
        (Nat.div_lt_iff_lt_mul (by omega)).mpr ht'⟩, mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.div_mul_le_self ..,?_⟩,hp⟩⟩
      have h := Nat.lt_mul_div_succ t (show 0 < B by omega)
      simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_comm B (t/B)] using h
  have hsize (j : ℕ) (hj : j ∈ J) : K*(S j).card ≤ 4*K^2*P.card+4*B := by
    have bounds := mem_Ico.mp hj
    have h := lucasFibonacciSum_smooth_interval_bound (S j) P r d (j*B) B hd
      (filter_subset ..) (fun t ht => (mem_filter.mp ht).2)
    have hleft : d*B*(K*(S j).card) ≤ d*(j*B)*(S j).card := by
      have e := Nat.mul_le_mul_right (S j).card (Nat.mul_le_mul_left (d*B) bounds.1)
      nlinarith only [e]
    have hupper : r + d*(j*B+B)+3 ≤ 2*(d*B)*K^2 := by
      have e := Nat.mul_le_mul_left (d*B) (show j+1 ≤ K^2 from bounds.2)
      have e' : B ≤ d*B*K^2 := by
        calc
          B ≤ d*B := by simpa using Nat.mul_le_mul_right B hd
          _ ≤ _ := Nat.le_mul_of_pos_right _ (pow_pos hK _)
      nlinarith only [e,e',hB]
    have hr := Nat.mul_le_mul_right P.card (Nat.mul_le_mul_left 2 hupper)
    apply Nat.le_of_mul_le_mul_left (c:=d*B) _ (Nat.mul_pos hd (by omega))
    nlinarith only [h,hleft,hr]
  have hcard : ((range (K^2*B)).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P).card ≤
      K*B + ∑ j ∈ J, (S j).card := by
    refine (card_le_card hpart).trans ((card_union_le ..).trans ?_)
    simpa only [card_range] using Nat.add_le_add_left (card_biUnion_le : (J.biUnion S).card ≤ _) (K*B)
  have hsum := sum_le_sum hsize
  rw [sum_const,nsmul_eq_mul,←mul_sum] at hsum
  have hJ : J.card ≤ K^2 := by simp [J]
  have hlarge := Nat.mul_le_mul_right (4*K^2*P.card+4*B) hJ
  apply Nat.le_of_mul_le_mul_left (c:=K) _ hK
  have hcount := Nat.mul_le_mul_left K hcard
  nlinarith only [hcount,hsum,hlarge]



/-- Any collection of o(N) candidate primes supports only o(N) of the first
N terms on each fixed positive-step progression. The set can vary with N. -/
theorem sparse_prime_support_density_zero (r d : ℕ) (hd : 0 < d) (P : ℕ → Finset ℕ)
    (hs : Filter.Tendsto (fun N : ℕ => ((P N).card : ℝ)/N) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ =>
      (((range N).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P N).card : ℝ)/N)
      Filter.atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (max 1 (20/ε))
  have hkR : 0 < (K:ℝ) := lt_trans (by norm_num : (0:ℝ)<1) ((le_max_left ..).trans_lt hK)
  have hk : 0 < K := by exact_mod_cast hkR
  have hsmall : 10/(K:ℝ) < ε/2 := by
    have := (div_lt_iff₀ hε).mp ((le_max_right ..).trans_lt hK)
    apply (div_lt_iff₀ hkR).mpr
    nlinarith
  have hlim : Filter.Tendsto (fun N : ℕ => 4*(K:ℝ)^3*(((P N).card : ℝ)/N)) Filter.atTop (nhds 0) := by
    simpa using hs.const_mul (4*(K:ℝ)^3)
  filter_upwards [Filter.eventually_ge_atTop ((r+3)*K^2),
    hlim.eventually_lt_const (show 0 < ε/2 by positivity)] with N hN hP
  let B := N/(K^2)+1
  have hk2 := pow_pos hk 2
  have hB : r+3 ≤ B := (Nat.le_div_iff_mul_le hk2).mpr hN |>.trans (Nat.le_succ _)
  have hcover : N ≤ K^2*B := (Nat.lt_mul_div_succ N hk2).le
  have hneg : K^2 ≤ N := by
    calc
      _ ≤ (r+3)*K^2 := by simpa using Nat.mul_le_mul_right (K^2) (show 1 ≤ r+3 by omega)
      _ ≤ _ := hN
  have hN' : 0 < N := hk2.trans_le hneg
  have hN'' : 0 < (N:ℝ) := by exact_mod_cast hN'
  have hbN : K^2*B ≤ 2*N := by
    dsimp [B]
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm (K^2)]
    have := Nat.div_mul_le_self N (K^2)
    omega
  let C := ((range N).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P N).card
  have hC : C ≤ 5*K*B+4*K^3*(P N).card := by
    refine (card_le_card (filter_subset_filter _ (range_mono hcover))).trans ?_
    exact tiled_smooth_count (P N) r d K B hd hk hB
  have hbr : (K:ℝ)^2 * B ≤ 2*N := by exact_mod_cast hbN
  have hcr : (C:ℝ) ≤ 5*(K:ℝ)*B+4*(K:ℝ)^3*(P N).card := by exact_mod_cast hC
  have hfirst : 5*(K:ℝ)*B/N ≤ 10/K := by
    rw [div_le_div_iff₀ hN'' hkR]
    nlinarith only [hbr]
  change dist ((C:ℝ)/N) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  calc
    (C:ℝ)/N ≤ (5*(K:ℝ)*B+4*(K:ℝ)^3*(P N).card)/N := by gcongr
    _ = 5*(K:ℝ)*B/N+4*(K:ℝ)^3*(((P N).card : ℝ)/N) := by ring
    _ < ε := by linarith only [hfirst,hP,hsmall]


open Filter
open scoped Topology

private lemma moving_threshold_smooth (r d : ℕ) (hd : 0 < d) (Y : ℕ → ℕ)
    (hy : Tendsto (fun t : ℕ => ((Y t).primeCounting : ℝ)/t) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (((range N).filter fun t =>
      ∀ p ∈ (lucasFibonacciSum (r+d*t)).primeFactors, p ≤ Y t).card : ℝ)/N) atTop (𝓝 0) := by
  let M (N : ℕ) := (range N).sup Y
  let P (N : ℕ) := (M N).primesLE
  have hsp : Tendsto (fun N : ℕ => ((P N).card : ℝ)/N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨L,hL⟩ := Metric.tendsto_atTop.mp hy ε hε
    let D := (M (L+1)).primeCounting
    have lim := tendsto_const_div_atTop_nhds_zero_nat (D:ℝ)
    filter_upwards [eventually_ge_atTop 1,lim.eventually_lt_const hε] with N hN hD
    obtain ⟨j,hj,he⟩ := exists_mem_eq_sup (range N) (by exact ⟨0,mem_range.mpr hN⟩) Y
    change dist (((M N).primesLE.card : ℝ)/N) 0 < ε
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),Nat.primesLE_card_eq_primeCounting]
    change M N = Y j at he
    rw [he]
    by_cases h : j ≤ L
    · have hj' : Y j ≤ M (L+1) := le_sup (f:=Y) (mem_range.mpr (by omega))
      have hj'' := Nat.monotone_primeCounting hj'
      exact lt_of_le_of_lt (by exact div_le_div_of_nonneg_right (by exact_mod_cast hj'') (by positivity)) hD
    · have hlim := hL j (by omega)
      change dist (((Y j).primeCounting : ℝ)/j) 0 < ε at hlim
      rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hlim
      exact lt_of_le_of_lt (div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast (show 0 < j by omega)) (by exact_mod_cast (mem_range.mp hj).le)) hlim
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (sparse_prime_support_density_zero r d hd P hsp)
  apply Eventually.of_forall
  intro N
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (show ((range N).filter fun t =>
    ∀ p ∈ (lucasFibonacciSum (r+d*t)).primeFactors, p ≤ Y t) ⊆
    (range N).filter fun t => (lucasFibonacciSum (r+d*t)).primeFactors ⊆ P N by
      intro t ht
      obtain ⟨ht,hsmall⟩ := mem_filter.mp ht
      refine mem_filter.mpr ⟨ht, fun p hp => Nat.mem_primesLE.mpr ⟨?_, Nat.prime_of_mem_primeFactors hp⟩⟩
      exact (hsmall p hp).trans (le_sup (f:=Y) ht))

/-- Chebyshev's estimate is uniform even when the cutoff oscillates.
Majorizing it by n ensures its logarithm is at least log n. -/
private lemma prime_count_threshold (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((⌊e n * n * Real.log n⌋₊).primeCounting : ℝ)/n) atTop (𝓝 0) := by
  let X (n : ℕ) := max (n:ℝ) (e n*n*Real.log n)
  have hX : Tendsto X atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_natCast_atTop_atTop
  let A := Real.log 4 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun n : ℕ => A*((Real.log n)⁻¹+|e n|)) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.comp hlog).add he.abs).const_mul A
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 2,hX.eventually (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num))] with n hn hπ
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hm : (n:ℝ) ≤ X n := le_max_left ..
  have hπ' : ((⌊e n*n*Real.log n⌋₊).primeCounting : ℝ) ≤ A*X n/Real.log n := by
    calc
      _ ≤ ((⌊X n⌋₊).primeCounting : ℝ) := by
        exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono (le_max_right ..))
      _ ≤ A*X n/Real.log (X n) := hπ
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hA.le (hn0.le.trans hm)) hl (Real.log_le_log hn0 hm)
  have hb : X n ≤ n + |e n| * n*Real.log n := by
    refine max_le ?_ ?_
    · have : 0 ≤ |e n| * n*Real.log n := by positivity
      linarith
    · have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self (e n)) hn0.le) hl.le
      linarith
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ A*X n/Real.log n := hπ'
    _ ≤ A*(n+|e n| * n*Real.log n)/Real.log n := by gcongr
    _ = A*((Real.log n)⁻¹+|e n|)*n := by field_simp

/-- Except on a set of indices of density zero, the canonical upper diagonal
has a prime divisor exceeding e(n)n log n, for each function e tending to zero. -/
theorem sub_n_log_n_smooth_density_zero (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (((range N).filter fun n =>
      ∀ p ∈ (lucasFibonacciSum n).primeFactors, (p : ℝ) ≤ e n*n*Real.log n).card : ℝ)/N)
      atTop (𝓝 0) := by
  have h := moving_threshold_smooth 0 1 (by decide) (fun n => ⌊e n*n*Real.log n⌋₊)
    (prime_count_threshold e he)
  simp only [one_mul,zero_add] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h
  apply Eventually.of_forall
  intro N
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (show ((range N).filter fun n => ∀ p ∈ (lucasFibonacciSum n).primeFactors, (p:ℝ) ≤ e n*n*Real.log n) ⊆ _ by
    intro n hn
    obtain ⟨hn,hh⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn,fun p hp => Nat.le_floor (hh p hp)⟩)


/-- The same threshold uses the actual Lucas–Fibonacci index on each
positive-step progression. -/
theorem progression_sub_n_log_n_smooth_density_zero (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (r d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (((range N).filter fun t =>
      ∀ p ∈ (lucasFibonacciSum (r+d*t)).primeFactors,
        (p : ℝ) ≤ e (r+d*t)*(r+d*t)*Real.log (r+d*t)).card : ℝ)/N) atTop (𝓝 0) := by
  classical
  let D := r+d+1
  let small (n : ℕ) : Prop := ∀ p ∈ (lucasFibonacciSum n).primeFactors, (p:ℝ) ≤ e n*n*Real.log n
  let A (n : ℕ) := ((range n).filter small).card
  have hD : 0 < D := by dsimp [D]; omega
  have hj : Tendsto (fun n : ℕ => D*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simpa using Nat.mul_le_mul_right n hD) tendsto_id
  have hlim : Tendsto (fun n : ℕ => (D:ℝ)*((A (D*n):ℝ)/(D*n:ℕ))) atTop (𝓝 0) := by
    simpa [A,small,Function.comp_apply] using ((sub_n_log_n_smooth_density_zero e he).comp hj).const_mul (D:ℝ)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  let T := (range n).filter fun t => small (r+d*t)
  have hc : T.card ≤ A (D*n) := by
    apply card_le_card_of_injOn (fun t => r+d*t)
    · intro t ht
      obtain ⟨ht,hv⟩ := mem_filter.mp ht
      refine mem_filter.mpr ⟨mem_range.mpr ?_,hv⟩
      have hr := Nat.mul_le_mul_left r hn
      have ht' := Nat.mul_le_mul_left d (mem_range.mp ht).le
      dsimp [D]; nlinarith
    · intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel h)
  simp only [←Nat.cast_mul,←Nat.cast_add]
  change (T.card:ℝ)/n ≤ _
  calc
    _ ≤ (A (D*n):ℝ)/n := by exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = (D:ℝ)*((A (D*n):ℝ)/(D*n:ℕ)) := by
      push_cast
      have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hD' : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      field_simp

#print axioms progression_sub_n_log_n_smooth_density_zero
#print axioms sub_n_log_n_smooth_density_zero
#print axioms sparse_prime_support_density_zero

#print axioms lucasFibonacciSum_prod_dvd_lcm_mul_fib
#print axioms lucasFibonacciSum_smooth_interval_bound

end Arxiv.«2211.10788»
