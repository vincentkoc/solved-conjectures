import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture
import research.arxiv.«1104.1579».CunninghamLocalPeriods
import Mathlib.NumberTheory.Chebyshev

/-! A logarithmic length bound for both signs from positive relative density at base two. -/

namespace CunninghamChain

open Filter Finset Real ArtinPrimitiveRootsConjecture
open scoped Topology

/-- Primes up to the cutoff for which two is a primitive root in the pinned Artin predicate. -/
noncomputable def artinPrimes (n : ℕ) : Finset ℕ := by
  classical exact (Nat.primesLE n).filter (· ∈ S 2)

private lemma mem_artinPrimes {q n : ℕ} : q ∈ artinPrimes n ↔ q ≤ n ∧ q ∈ S 2 := by
  classical
  simp only [artinPrimes, mem_filter, Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2⟩⟩

private lemma relative_count {δ : ℝ} (hδ : 0 < δ)
    (hd : (S 2).HasDensity δ {p | p.Prime}) :
    ∀ᶠ n : ℕ in atTop, δ / 2 * n.primeCounting ≤ (artinPrimes n).card := by
  classical
  have h := (hd.eventually (eventually_gt_nhds (show δ / 2 < δ by linarith)))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually h] with n hn
  have hA : ((S 2 ∩ {p : ℕ | p.Prime}) ∩ Set.Iio (n + 1)) = ↑(artinPrimes n) := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_ofPred_eq, Finset.mem_coe,
      mem_artinPrimes, Nat.lt_succ_iff]
    exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, h.2.1⟩, h.1⟩⟩
  have hB : ({p : ℕ | p.Prime} ∩ Set.Iio (n + 1)) = ↑(Nat.primesLE n) := by
    ext q
    simp [Nat.mem_primesLE, and_comm]
  change δ / 2 < (S 2).partialDensity {p | p.Prime} (n + 1) at hn
  rw [Set.partialDensity, hA, hB, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Nat.primesLE_card_eq_primeCounting] at hn
  by_cases hzero : n.primeCounting = 0
  · simp [hzero]
  exact ((lt_div_iff₀ (by positivity)).mp hn).le

private lemma small_prime_weight (n : ℕ) :
    ((artinPrimes n).card : ℝ) * (log n / 2) ≤
      (∑ q ∈ artinPrimes n, log q) + √n * (log n / 2) := by
  classical
  rw [← log_sqrt (Nat.cast_nonneg n)]
  calc
    _ = ∑ _q ∈ artinPrimes n, log √n := by simp
    _ ≤ ∑ q ∈ artinPrimes n, (log q + if (q : ℝ) ≤ √n then log √n else 0) := by
      apply sum_le_sum
      intro q hq
      split_ifs with h
      · linarith [log_natCast_nonneg q]
      · have hx : 0 < (n : ℝ) := by
          exact_mod_cast (mem_artinPrimes.mp hq).2.1.pos.trans_le (mem_artinPrimes.mp hq).1
        simpa using (log_le_log (sqrt_pos.mpr hx)
          (le_of_not_ge h))
    _ ≤ _ := by
      rw [sum_add_distrib, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      have hcard : (((artinPrimes n).filter (fun q : ℕ => (q : ℝ) ≤ √n)).card : ℝ) ≤ √n := by
        apply le_trans _ (Nat.floor_le (sqrt_nonneg _))
        norm_cast
        rw [show ⌊√(n : ℝ)⌋₊ = (Icc 1 ⌊√(n : ℝ)⌋₊).card by simp]
        apply card_le_card
        intro q hq
        obtain ⟨hq, hlt⟩ := mem_filter.mp hq
        exact mem_Icc.mpr ⟨(mem_artinPrimes.mp hq).2.1.one_le, Nat.le_floor hlt⟩
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right hcard
      rw [log_sqrt (Nat.cast_nonneg n)]
      positivity

private lemma weight_growth {δ : ℝ} (hδ : 0 < δ)
    (hd : (S 2).HasDensity δ {p | p.Prime}) :
    ∀ᶠ n : ℕ in atTop, (δ * log 2 / 16) * n ≤ ∑ q ∈ artinPrimes n, log q := by
  have htwo : 0 < log 2 := log_pos (by norm_num)
  have hlog := (isLittleO_log_id_atTop.def (show 0 < log 2 / 4 by positivity))
  have hroot := (isLittleO_log_rpow_atTop (show 0 < (1 / 2 : ℝ) by norm_num)).def
    (show 0 < δ * log 2 / 8 by positivity)
  have hsucc : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [relative_count hδ hd, hsucc.eventually hlog,
    tendsto_natCast_atTop_atTop.eventually hroot, eventually_ge_atTop 2] with n hcount hsmall hsq hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < log n := log_pos (by linarith)
  have hlogp : 0 ≤ log ((n : ℝ) + 1) := log_nonneg (by linarith)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlogp,
    abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)] at hsmall
  simp only [← sqrt_eq_rpow, Real.norm_eq_abs, abs_of_pos hlogn, abs_of_nonneg (sqrt_nonneg _)] at hsq
  have hpi := (div_le_iff₀ hlogn).mp (Chebyshev.pi_ge n)
  have hmain : n * log 2 / 2 ≤ (n.primeCounting : ℝ) * log n := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) htwo.le]
  have herr := mul_le_mul_of_nonneg_left hsq (sqrt_nonneg (n : ℝ))
  have hbalance := small_prime_weight n
  nlinarith only [hbalance, mul_le_mul_of_nonneg_left hmain hδ.le,
    mul_le_mul_of_nonneg_right hcount hlogn.le, herr,
    congrArg (fun x : ℝ => δ * log 2 * x) (sq_sqrt (Nat.cast_nonneg n))]

private lemma prime_product_dvd (n m : ℕ) (h : ∀ q ∈ artinPrimes n, q ∣ m) :
    (∏ q ∈ artinPrimes n, q) ∣ m := by
  apply Finset.prod_dvd_of_isRelPrime _ h
  intro a ha b hb hab
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
    (mem_artinPrimes.mp ha).2.1 (mem_artinPrimes.mp hb).2.1).mpr hab)

private lemma artin_odd {q : ℕ} (hq : q ∈ S 2) : 2 < q := by
  have hp := hq.1.two_le
  by_contra! he
  obtain rfl : q = 2 := by omega
  have ho := hq.2
  change orderOf ((2 : ℤ) : ZMod 2) = 1 at ho
  rw [show ((2 : ℤ) : ZMod 2) = 0 by decide, orderOf_zero] at ho
  omega

private lemma forced_shift {p k q : ℕ} (hq : q ∈ S 2) (hqk : q ≤ k) (hkp : k < p)
    (t : ℕ → ℕ) (ht : ∀ i, p ≤ t i) (hp : ∀ i < k, (t i).Prime)
    (s : ZMod q) (hit : s ^ orderOf (2 : ZMod q) = 1 →
      ∃ i < orderOf (2 : ZMod q), q ∣ t i) : s = 0 := by
  let : Fact q.Prime := ⟨hq.1⟩
  have ho : orderOf (2 : ZMod q) = q - 1 := by simpa using hq.2
  by_contra hs
  obtain ⟨i, hi, hdiv⟩ := hit (ho ▸ ZMod.pow_card_sub_one_eq_one hs)
  have he := (Nat.prime_dvd_prime_iff_eq hq.1 (hp i (by omega))).mp hdiv
  have := ht i
  omega

/-- Every base-two primitive-root prime up to the length divides the first-kind
shifted seed when the prime prefix is shorter than its seed. -/
theorem firstKind_artin_product_dvd {p k : ℕ} (hkp : k < p)
    (hc : ∀ i < k, (firstKindTerm p i).Prime) : (∏ q ∈ artinPrimes k, q) ∣ p + 1 := by
  apply prime_product_dvd
  intro q hq
  obtain ⟨hqk, hq⟩ := mem_artinPrimes.mp hq
  let : Fact q.Prime := ⟨hq.1⟩
  have hz := forced_shift hq hqk hkp (firstKindTerm p) (fun i => by
    induction i with
    | zero => rfl
    | succ i ih => simp only [firstKindTerm]; omega) hc _
    (firstKind_dvd_in_period_iff (artin_odd hq) p).mpr
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa using hz

/-- For the second sign the same product divides the preceding natural number. -/
theorem secondKind_artin_product_dvd {p k : ℕ} (hkp : k < p)
    (hc : ∀ i < k, (secondKindTerm p i).Prime) : (∏ q ∈ artinPrimes k, q) ∣ p - 1 := by
  apply prime_product_dvd
  intro q hq
  obtain ⟨hqk, hq⟩ := mem_artinPrimes.mp hq
  let : Fact q.Prime := ⟨hq.1⟩
  have hz := forced_shift hq hqk hkp (secondKindTerm p) (fun i => by
    induction i with
    | zero => rfl
    | succ i ih => simp only [secondKindTerm]; omega) hc _
    (secondKind_dvd_in_period_iff (artin_odd hq) p (by omega)).mpr
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero]
  exact (sub_eq_zero.mp hz).symm

private lemma short_or_below_seed {p k : ℕ}
    (hc : IsFirstKindChainOfLength p k ∨ IsSecondKindChainOfLength p k) (hk : 6 ≤ k) :
    k < p := by
  by_contra! h
  have hs : p ≤ 4 * k := by omega
  rcases hc with hc | hc
  · have he := (firstKind_quarter_exceptions p k).mp ⟨hc, hs⟩
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at he
    omega
  · have he := (secondKind_quarter_exceptions p k).mp ⟨hc, hs⟩
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at he
    omega

/-- Positive relative density for base two in Artin's conjecture gives one
logarithmic length bound for exact Cunningham chains of either kind. -/
theorem logarithmic_length_of_artin_two
    (hd : (S 2).HasPosDensity {p | p.Prime}) :
    ∃ C : ℝ, 0 < C ∧ ∀ p k : ℕ,
      IsFirstKindChainOfLength p k ∨ IsSecondKindChainOfLength p k →
      (k : ℝ) ≤ C * log p := by
  obtain ⟨δ, hδ, hd⟩ := hd
  let c := δ * log 2 / 16
  have htwo : 0 < log 2 := log_pos (by norm_num)
  have hcpos : 0 < c := by dsimp [c]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (weight_growth hδ hd)
  let M : ℕ := max 6 N
  let C := max ((M : ℝ) / log 2) (2 / c)
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < 2 / c) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro p k hc
  have hp : 2 ≤ p := by
    rcases hc with hc | hc
    · exact (hc.2.1 0 hc.1).two_le
    · exact (hc.2.1 0 hc.1).two_le
  have hlp : log 2 ≤ log p := log_le_log (by norm_num) (by exact_mod_cast hp)
  by_cases hk : k < M
  · calc
      (k : ℝ) ≤ M := by exact_mod_cast hk.le
      _ = ((M : ℝ) / log 2) * log 2 := (div_mul_cancel₀ _ htwo.ne').symm
      _ ≤ C * log p := mul_le_mul (le_max_left _ _) hlp htwo.le hC.le
  · have hM : M ≤ k := by omega
    have hkp := short_or_below_seed hc ((le_max_left _ _).trans hM)
    have hg := hN k ((le_max_right _ _).trans hM)
    have hprod : (∏ q ∈ artinPrimes k, q) ≤ p + 1 := by
      rcases hc with hc | hc
      · exact Nat.le_of_dvd (by omega) (firstKind_artin_product_dvd hkp hc.2.1)
      · exact (Nat.le_of_dvd (by omega) (secondKind_artin_product_dvd hkp hc.2.1)).trans (by omega)
    have hprod_pos : 0 < ∏ q ∈ artinPrimes k, q :=
      prod_pos fun q hq => (mem_artinPrimes.mp hq).2.1.pos
    have hweight : (∑ q ∈ artinPrimes k, log q) ≤ 2 * log p := calc
      _ = log ((∏ q ∈ artinPrimes k, q : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod (fun q hq => by
          exact_mod_cast (mem_artinPrimes.mp hq).2.1.ne_zero)]
      _ ≤ log ((p : ℝ) ^ 2) := by
        apply log_le_log (by exact_mod_cast hprod_pos)
        exact_mod_cast hprod.trans (by nlinarith [Nat.mul_le_mul_right p hp] : p + 1 ≤ p ^ 2)
      _ = _ := by rw [log_pow]; norm_num
    calc
      (k : ℝ) ≤ (2 / c) * log p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
        simpa only [mul_comm c] using (show c * k ≤ 2 * log p from hg.trans hweight)
      _ ≤ C * log p := mul_le_mul_of_nonneg_right (le_max_right _ _) (htwo.le.trans hlp)

/-- Direct specialization of the pinned universal Artin part (i) statement. -/
theorem logarithmic_length_of_artin
    (hArtin : type_of% ArtinPrimitiveRootsConjecture.artin_primitive_roots.parts.i) :
    ∃ C : ℝ, 0 < C ∧ ∀ p k : ℕ,
      IsFirstKindChainOfLength p k ∨ IsSecondKindChainOfLength p k →
      (k : ℝ) ≤ C * log p :=
  logarithmic_length_of_artin_two (hArtin 2 (show Prime (2 : ℤ) by norm_num).not_isSquare (by norm_num))

#print axioms firstKind_artin_product_dvd
#print axioms secondKind_artin_product_dvd
#print axioms logarithmic_length_of_artin_two
#print axioms logarithmic_length_of_artin

end CunninghamChain
