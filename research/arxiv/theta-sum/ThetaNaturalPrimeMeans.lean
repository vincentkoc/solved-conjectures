import ThetaHalfLogExcursions

/-! Transfer from von Mangoldt means to natural counts for selected primes. -/

namespace Arxiv.«2501.03234».ThetaNaturalPrimeMeans

open Finset Filter ArithmeticFunction ThetaPrimeDensity
open scoped Topology

/-- The part of the von Mangoldt sum supported on a selected set, with the
exclusive endpoint used by `WeakPNT_AP` in `PrimeNumberTheoremAnd.Wiener`. -/
noncomputable def selectedPsi (P : ℕ → Prop) (N : ℕ) : ℝ := by
  classical exact ∑ n ∈ range N, if P n then vonMangoldt n else 0

/-- The von Mangoldt weight on higher prime powers bounds the discrepancy from
the prime logarithmic weight, independently of the selected set. -/
theorem selected_prime_weight_bounds (P : ℕ → Prop) (N : ℕ) :
    let T := ∑ p ∈ primeSet P N, Real.log p
    T ≤ selectedPsi P (N+1) ∧ selectedPsi P (N+1)-T ≤ Chebyshev.psi N-Chebyshev.theta N := by
  classical
  let T := ∑ p ∈ primeSet P N, Real.log p
  have hsplit : selectedPsi P (N+1) - T =
      ∑ n ∈ (range (N+1)).filter (fun n => ¬ n.Prime), if P n then vonMangoldt n else 0 := by
    simp only [selectedPsi, T, primeSet, Nat.primesLE_eq_filter_range, sum_filter,
      ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hp : n.Prime <;> by_cases hs : P n <;>
      simp [hp, hs, vonMangoldt_apply_prime]
  have hpower : selectedPsi P (N+1) - T ≤ Chebyshev.psi N - Chebyshev.theta N := by
    rw [hsplit, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    simp only [Nat.floor_natCast, Nat.range_succ_eq_Icc_zero, sum_filter, ← sum_sub_distrib]
    apply sum_le_sum
    intro n _
    by_cases hp : n.Prime <;> by_cases hs : P n <;>
      simp [hp, hs, vonMangoldt_apply_prime, vonMangoldt_nonneg]
  have hT : T ≤ selectedPsi P (N+1) := by
    apply sub_nonneg.mp
    rw [hsplit]
    exact sum_nonneg fun n _ => by split_ifs <;> simp [vonMangoldt_nonneg]
  exact ⟨hT,hpower⟩

#print axioms selected_prime_weight_bounds

/-- The signed difference between the weighted sum and its prime-count
approximation is trapped between two errors independent of the selection. -/
theorem selected_count_bounds (P : ℕ → Prop) (N : ℕ) :
    let E := ((primeSet P N).card : ℝ) * Real.log N - selectedPsi P (N+1);
    -(Chebyshev.psi N - Chebyshev.theta N) ≤ E ∧
      E ≤ (N.primeCounting : ℝ) * Real.log N - Chebyshev.theta N := by
  classical
  obtain ⟨hT,hpower⟩ := selected_prime_weight_bounds P N
  have hlog (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      0 ≤ Real.log N - Real.log p :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos)
      (by exact_mod_cast Nat.le_of_mem_primesLE hp))
  have hinc : ∑ p ∈ primeSet P N, (Real.log N - Real.log p) ≤
      ∑ p ∈ Nat.primesLE N, (Real.log N - Real.log p) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp _ => hlog p hp)
  have hpos : 0 ≤ ∑ p ∈ primeSet P N, (Real.log N - Real.log p) :=
    sum_nonneg fun p hp => hlog p (filter_subset _ _ hp)
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting,
    ← Chebyshev.theta_eq_sum_primesLE_log] at hinc hpos
  change _ ≤ (primeSet P N).card * Real.log N - selectedPsi P (N+1) ∧ _
  constructor <;> linarith

#print axioms selected_count_bounds

/-- The comparison error is sublinear even if the selection changes with
the endpoint. In particular no uniformity in the prime number theorem for
arithmetic progressions is needed for this change of weight. -/
theorem selected_count_error (P : ℕ → ℕ → Prop) :
    Tendsto (fun N : ℕ => (((primeSet (P N) N).card : ℝ) * Real.log N -
      selectedPsi (P N) (N+1)) / N) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨C, hC⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.bound
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((Real.tendsto_sqrt_atTop.comp hn).const_div_atTop (-K))
    ((Real.tendsto_log_atTop.comp hn).const_div_atTop C)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have h : 0 < (N : ℝ) := by positivity
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr h
    apply (div_le_div_iff₀ hs h).2
    have hl := (selected_count_bounds (P N) N).1
    have hw := hK (N : ℝ)
    have hmul := mul_le_mul_of_nonneg_right ((neg_le_neg hw).trans hl) hs.le
    calc -K * (N : ℝ) = -(K * Real.sqrt N) * Real.sqrt N := by
          rw [neg_mul, neg_mul, mul_assoc, Real.mul_self_sqrt h.le]
         _ ≤ _ := hmul
  · filter_upwards [eventually_gt_atTop 1, hn.eventually hC] with N hN hbound
    have hx : 1 < (N : ℝ) := by exact_mod_cast hN
    have h := zero_lt_one.trans hx
    have hlog := Real.log_pos hx
    simp only [Nat.floor_natCast, Real.norm_eq_abs] at hbound
    rw [abs_of_nonneg (div_nonneg h.le (sq_nonneg _))] at hbound
    have hb := (le_abs_self _).trans hbound
    have hc := (selected_count_bounds (P N) N).2
    calc _ ≤ ((N.primeCounting : ℝ) * Real.log N - Chebyshev.theta N) / N :=
          div_le_div_of_nonneg_right hc h.le
         _ = ((N.primeCounting : ℝ) - Chebyshev.theta N / Real.log N) * Real.log N / N := by
          field_simp
         _ ≤ (C * ((N : ℝ) / Real.log N ^ 2)) * Real.log N / N := by
          gcongr
         _ = C / Real.log N := by field_simp

#print axioms selected_count_error

/-- Remove von Mangoldt weights, preserving the limit and accounting for
the exclusive endpoint in the original weighted mean. -/
theorem prime_count_of_mangoldt {P : ℕ → Prop} {L : ℝ}
    (hP : Tendsto (fun N : ℕ => selectedPsi P N / N) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ((primeSet P N).card : ℝ) * Real.log N / N) atTop (𝓝 L) := by
  have hr : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hshift := (hP.comp (tendsto_add_atTop_nat 1)).mul hr
  have h := (selected_count_error (fun _ => P)).add hshift
  rw [mul_one, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  change (_ - _) / (N : ℝ) + (selectedPsi P (N+1) / ((N+1 : ℕ) : ℝ)) *
    (1 + 1 / (N : ℝ)) = _
  push_cast
  field_simp
  ring

/-- Arithmetic-progression input in the form of `WeakPNT_AP` at the
matching Lean 4.33.1 revision of PrimeNumberTheoremAnd. -/
def ProgressionMangoldt : Prop := ∀ {q a : ℕ}, 1 ≤ q → a.Coprime q → a < q →
    Tendsto (fun N : ℕ => selectedPsi (fun n => n % q = a) N / N)
      atTop (𝓝 (1 / (q.totient : ℝ)))

/-- Natural prime density of each reduced residue class from the
progression von Mangoldt asymptotic, including normalization by π(N). -/
theorem class_prime_density (hAP : ProgressionMangoldt) {q a : ℕ}
    (hq : 1 ≤ q) (ha : a.Coprime q) (hlt : a < q) :
    Tendsto (fun N : ℕ => ((primeSet (fun n => n % q = a) N).card : ℝ) / N.primeCounting)
      atTop (𝓝 (1 / (q.totient : ℝ))) := by
  have hall := prime_count_of_mangoldt (hAP (q := 1) (a := 0) (by decide) (by decide) (by decide))
  have hπ : Tendsto (fun N : ℕ => (N.primeCounting : ℝ) * Real.log N / N) atTop (𝓝 1) := by
    simpa [primeSet, Nat.mod_one, Nat.primesLE_card_eq_primeCounting] using hall
  have h := (prime_count_of_mangoldt (hAP hq ha hlt)).div hπ one_ne_zero
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hl := Real.log_pos (show (1 : ℝ) < N by exact_mod_cast hN)
  simp only [Pi.div_apply]
  field_simp

#print axioms prime_count_of_mangoldt
#print axioms class_prime_density

open ThetaConditionalRows ThetaPeriodMeans

/-- The unweighted mean over every prime up to the inclusive endpoint. -/
noncomputable def primeMean (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, f p) / N.primeCounting

private theorem nonunit_class {q a : ℕ} (hq : 0 < q) (ha : ¬ a.Coprime q) :
    Tendsto (fun N : ℕ => ((primeSet (fun n => n % q = a) N).card : ℝ) / N.primeCounting)
      atTop (𝓝 0) := by
  classical
  have hπ := (tendsto_natCast_atTop_atTop (R := ℝ)).comp Nat.tendsto_primeCounting
  apply (hπ.const_div_atTop ((primeSet (fun n => n % q = a) q).card : ℝ)).congr'
  filter_upwards [eventually_ge_atTop q] with N hN
  have he : primeSet (fun n => n % q = a) q = primeSet (fun n => n % q = a) N := by
    ext p
    simp only [primeSet, mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hp,hprime⟩,hmod⟩
      exact ⟨⟨hp.trans hN,hprime⟩,hmod⟩
    · rintro ⟨⟨_,hprime⟩,hmod⟩
      have hnc : ¬ p.Coprime q := by
        intro hc
        apply ha
        rw [← hmod, ← ZMod.isUnit_iff_coprime, ZMod.natCast_mod, ZMod.isUnit_iff_coprime]
        exact hc
      exact ⟨⟨Nat.le_of_dvd hq (not_not.mp (hprime.coprime_iff_not_dvd.not.mp hnc)),hprime⟩,hmod⟩
  rw [he]
  rfl

/-- Equidistribution for every fixed periodic real test function. The finitely
many prime divisors of the modulus are included in the prime mean. -/
theorem periodic_prime_mean (hAP : ProgressionMangoldt) {q : ℕ} [NeZero q]
    {f : ℕ → ℝ} (hf : OnMod q f) :
    Tendsto (primeMean f) atTop (𝓝 (unitMean q f)) := by
  classical
  let C (a N : ℕ) := ((primeSet (fun n => n % q = a) N).card : ℝ) / N.primeCounting
  have hc (a : ℕ) (ha : a ∈ range q) :
      Tendsto (fun N => f a * C a N) atTop (𝓝 (if a.Coprime q then f a / q.totient else 0)) := by
    by_cases h : a.Coprime q
    · rw [if_pos h]
      simpa only [C,div_eq_mul_inv,one_mul] using
        (class_prime_density hAP (NeZero.pos q) h (mem_range.mp ha)).const_mul (f a)
    · simpa [h,C] using (nonunit_class (NeZero.pos q) h).const_mul (f a)
  have H := tendsto_finsetSum (range q) hc
  have hsum (N : ℕ) : (∑ a ∈ range q, f a * C a N) = primeMean f N := by
    simp only [C, ← mul_div_assoc, ← sum_div, primeMean]
    congr 1
    calc ∑ a ∈ range q, f a * ((primeSet (fun n => n % q = a) N).card : ℝ) =
          ∑ a ∈ range q, ∑ p ∈ Nat.primesLE N, if p % q = a then f a else 0 := by
            apply sum_congr rfl
            intro a _
            rw [← sum_filter]
            simp [primeSet,mul_comm]
            left
            congr 1
            ext p
            simp
         _ = _ := by
            rw [sum_comm]
            apply sum_congr rfl
            intro p _
            simpa [eq_comm, Nat.mod_lt p (NeZero.pos q)] using hf p
  have hlim : (∑ a ∈ range q, if a.Coprime q then f a / (q.totient : ℝ) else 0) =
      unitMean q f := by
    rw [← sum_filter,unitMean,ThetaReciprocalFibers.unit_sum_nat, sum_div]
  simpa only [hsum,hlim] using H

#print axioms periodic_prime_mean

open ThetaPrimeTailTransfer ThetaDivisibleDiagonal ThetaDiagonalConstant

private theorem primeCounting_atTop :
    Tendsto (fun N : ℕ => (N.primeCounting : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting

/-- The complete off-diagonal has mean zero over all primes. -/
theorem scaledOff_prime_mean (hAP : ProgressionMangoldt) :
    Tendsto (primeMean scaledOff) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,V,_,_,herr⟩ := prime_model_absolute (half_pos hε)
  let M := T.factorial
  let : NeZero M := ⟨(Nat.factorial_pos T).ne'⟩
  have hd (d : ℕ) (h : d ∈ Icc 2 T) (_ : Odd d) : d ∣ M :=
    Nat.dvd_factorial (by have := (mem_Icc.mp h).1; omega) (mem_Icc.mp h).2
  have hper : OnMod M (model T V) := low_onMod hd _ _
  have hz : unitMean M (model T V) = 0 := low_mean_zero hd _ _
  have hlim := periodic_prime_mean hAP hper
  rw [hz] at hlim
  filter_upwards [herr, Metric.tendsto_nhds.mp hlim (ε/2) (half_pos hε),
    primeCounting_atTop.eventually_gt_atTop 0] with N he hm hpos
  rw [Real.dist_eq,sub_zero] at hm ⊢
  have hclose : |primeMean scaledOff N - primeMean (model T V) N| ≤ ε/2 := by
    rw [primeMean,primeMean,← sub_div,← sum_sub_distrib,abs_div,abs_of_pos hpos,div_le_iff₀ hpos]
    exact (abs_sum_le_sum_abs _ _).trans he
  have ht := abs_add_le (primeMean scaledOff N - primeMean (model T V) N) (primeMean (model T V) N)
  rw [sub_add_cancel] at ht
  linarith

/-- A function converging along the primes has the same ordinary prime mean limit. -/
theorem prime_mean_of_convergence {f : ℕ → ℝ} {L : ℝ}
    (hf : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, n.Prime → |f n - L| < ε) :
    Tendsto (primeMean f) atTop (𝓝 L) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hf (ε/2) (half_pos hε))
  let B := ∑ n ∈ range A, |f n-L|
  have hb := (primeCounting_atTop.const_div_atTop B).eventually_lt_const (half_pos hε)
  filter_upwards [hb, primeCounting_atTop.eventually_gt_atTop 0] with N htail hpos
  have point (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      |f p-L| ≤ (if p < A then |f p-L| else 0) + ε/2 := by
    split_ifs with h
    · linarith
    · simpa using (hA p (le_of_not_gt h) (Nat.prime_of_mem_primesLE hp)).le
  have hhead : ∑ p ∈ (Nat.primesLE N).filter (· < A), |f p-L| ≤ B :=
    sum_le_sum_of_subset_of_nonneg (fun p hp => mem_range.mpr (mem_filter.mp hp).2)
      (fun p _ _ => abs_nonneg _)
  have hsum := sum_le_sum point
  simp only [sum_add_distrib,← sum_filter,sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting] at hsum
  have htail' := (div_lt_iff₀ hpos).mp htail
  rw [Real.dist_eq,primeMean,div_sub' hpos.ne',abs_div,abs_of_pos hpos,div_lt_iff₀ hpos]
  have hconst : ∑ _p ∈ Nat.primesLE N, L = N.primeCounting * L := by
    simp [Nat.primesLE_card_eq_primeCounting,mul_comm]
  rw [← hconst, ← sum_sub_distrib]
  have htri := abs_sum_le_sum_abs (fun p => f p - L) (Nat.primesLE N)
  linarith

/-- Ordinary prime mean of the second term for the original integer theta sum. -/
theorem S_second_order_prime_mean (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => (S p : ℝ)/p - Real.log p/2))
      atTop (𝓝 diagonalConstant) := by
  let f (p : ℕ) := (S p : ℝ)/p - Real.log p/2 - (8/Real.pi^2) * scaledOff p
  have hbase : Tendsto (primeMean f) atTop (𝓝 diagonalConstant) := by
    apply prime_mean_of_convergence
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp diagonal_second_order ε hε, eventually_gt_atTop 2] with p h hp hprime
    let : Fact p.Prime := ⟨hprime⟩
    have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
    have he : f p = divisibleDiagonal p / p - Real.log p/2 := by
      dsimp only [f,scaledOff]
      rw [S_eq_diagonal_add_offDiagonal hodd,add_div]
      field_simp [Real.pi_ne_zero]
      ring
    simpa only [he,Real.dist_eq] using h
  have h := hbase.add ((scaledOff_prime_mean hAP).const_mul (8/Real.pi^2))
  rw [mul_zero,add_zero] at h
  apply h.congr'
  apply Eventually.of_forall
  intro N
  change primeMean f N + _ * primeMean scaledOff N = _
  simp only [primeMean,← mul_div_assoc,← add_div,mul_sum,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro p _
  dsimp only [f]
  ring

#print axioms scaledOff_prime_mean
#print axioms S_second_order_prime_mean

open ThetaOffDiagonalSigns ThetaHalfLogExcursions

/-- At every sufficiently large endpoint, a fixed positive fraction of all
primes satisfy the predicate. -/
def PositiveLowerPrimeDensity (P : ℕ → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop, δ * Nat.primeCounting X ≤ ((primeSet P X).card : ℝ)

theorem lower_density_of_witness (hAP : ProgressionMangoldt) {P : ℕ → Prop}
    (hP : PeriodicWitness P) : PositiveLowerPrimeDensity P := by
  obtain ⟨q,hq,g,hg,hm,δ,hδ,H⟩ := hP
  refine ⟨δ,hδ,?_⟩
  filter_upwards [H,(periodic_prime_mean hAP hg).eventually_const_lt hm,
    primeCounting_atTop.eventually_gt_atTop 0] with X hX hmean hπ
  apply hX
  exact (div_pos_iff_of_pos_right hπ).mp hmean

/-- Both signed linear excursions of the original sum occur on positive
fractions of the primes at every sufficiently large endpoint. -/
theorem S_half_log_lower_densities (hAP : ProgressionMangoldt) :
    PositiveLowerPrimeDensity (fun p => p%24=1 ∧ (p:ℝ)*Real.log p/2+13*(p:ℝ)/50<(S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => p%24=17 ∧ (S p:ℝ)<(p:ℝ)*Real.log p/2-(p:ℝ)/1000) :=
  ⟨lower_density_of_witness hAP S_half_log_witnesses.1,
   lower_density_of_witness hAP S_half_log_witnesses.2⟩

#print axioms prime_mean_of_convergence
#print axioms lower_density_of_witness
#print axioms S_half_log_lower_densities

end Arxiv.«2501.03234».ThetaNaturalPrimeMeans
