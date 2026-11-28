import ThetaUniformWindows
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! Ordinary harmonic prefixes for nonprincipal characters at the edge of absolute convergence. -/
namespace Arxiv.«2501.03234».ThetaCharacterHarmonicLimit
open Finset Filter Topology

private theorem block {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (K : ℕ) : ∑ i ∈ range q, χ ((K+i:ℕ) : ZMod q) = 0 := by
  have hZ : ∑ x : ZMod q, χ ((K : ZMod q) + x) = 0 :=
    (Equiv.sum_comp (Equiv.addLeft (K : ZMod q)) fun x => χ x).trans (χ.sum_eq_zero_of_ne_one hχ)
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    change ∑ i : Fin (q+1), χ (((K+(i:ℕ)):ℕ) : ZMod (q+1)) = 0
    simp only [Nat.cast_add]
    change ∑ i : ZMod (q+1), χ ((K : ZMod (q+1)) + (i.val : ZMod (q+1))) = 0
    simpa only [ZMod.natCast_zmod_val] using hZ

private theorem interval {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (K n : ℕ) : ‖∑ i ∈ range n, χ ((K+i:ℕ) : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : q ≤ n
    · have hp := NeZero.pos q
      have hs := sum_range_add (fun i => χ ((K+i:ℕ) : ZMod q)) q (n-q)
      rw [Nat.add_sub_of_le hn, block χ hχ, zero_add] at hs
      rw [hs]
      simpa only [Nat.cast_add, ZMod.natCast_self, zero_add] using ih (n-q) (by omega)
    · apply (norm_sum_le ..).trans
      exact (sum_le_sum (s := range n) (fun i _ => χ.norm_le_one ((K+i:ℕ) : ZMod q))).trans
        (by simpa using (show (n:ℝ) ≤ q by exact_mod_cast (by omega : n ≤ q)))

private theorem weighted_interval {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {K : ℕ} (hK : 0 < K) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ‖∑ i ∈ range n, LSeries.term (fun j : ℕ => χ (j : ZMod q)) s (K+i)‖ ≤ q / (K:ℝ) := by
  let w (i : ℕ) := ((K+i:ℕ):ℝ) ^ (-s)
  have hweight (i : ℕ) : LSeries.term (fun j : ℕ => χ (j : ZMod q)) s (K+i) =
      w i • χ ((K+i:ℕ) : ZMod q) := by
    rw [LSeries.term_of_ne_zero (by omega), Complex.real_smul, mul_comm]
    simp only [w, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
      Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv]
  simp_rw [hweight]
  apply (ThetaUniformWindows.weighted_prefix _ w q (fun i => Real.rpow_nonneg (by positivity) _)
    (fun i j hij => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast Nat.add_le_add_left hij K) (by linarith)) (interval χ hχ K) n).trans
  simp only [w, Nat.add_zero, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg q)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK) (by linarith)

private theorem tail_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {K : ℕ} (hK : 0 < K) {s : ℝ} (hs : 1 < s) :
    ‖DirichletCharacter.LFunction χ (s:ℂ) -
      ∑ i ∈ range K, LSeries.term (fun j : ℕ => χ (j : ZMod q)) s i‖ ≤ q / (K:ℝ) := by
  let f (i : ℕ) := LSeries.term (fun j : ℕ => χ (j : ZMod q)) s i
  have hs' : 1 < (s:ℂ).re := hs
  have ht := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs').LSeriesHasSum.tendsto_sum_nat
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs'] at ht
  apply le_of_tendsto ((ht.sub_const (∑ i ∈ range K, f i)).norm)
  filter_upwards [eventually_ge_atTop K] with n hn
  change ‖(∑ i ∈ range n, f i) - ∑ i ∈ range K, f i‖ ≤ _
  have he := sum_range_add f K (n-K)
  rw [Nat.add_sub_of_le hn] at he
  rw [he, add_sub_cancel_left]
  exact weighted_interval χ hχ hK hs.le _

/-- Uniform truncation at the boundary, despite the failure of absolute convergence there. -/
theorem harmonic_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {K : ℕ} (hK : 0 < K) :
    ‖DirichletCharacter.LFunction χ 1 - ∑ i ∈ range K, χ (i : ZMod q) / (i:ℂ)‖ ≤ q / (K:ℝ) := by
  let f (s : ℝ) (i : ℕ) := LSeries.term (fun j : ℕ => χ (j : ZMod q)) s i
  have hc : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ (s:ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ 1)) := by
    simpa [Function.comp_def] using (((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal).continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have ht (i : ℕ) : Tendsto (fun s : ℝ => f s i) (𝓝[>] 1) (𝓝 (χ (i : ZMod q) / (i:ℂ))) := by
    by_cases hi : i = 0
    · simp [hi,f]
    · let : NeZero (i:ℂ) := ⟨Nat.cast_ne_zero.mpr hi⟩
      simp only [f, LSeries.term_of_ne_zero hi]
      have h := (continuous_const_cpow (i:ℂ)).comp Complex.continuous_ofReal
      have hh : Tendsto (fun s : ℝ => (i:ℂ) ^ (s:ℂ)) (𝓝[>] 1) (𝓝 (i:ℂ)) := by
        simpa [Function.comp_def] using (h.continuousAt (x := (1:ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
      exact tendsto_const_nhds.div hh (Nat.cast_ne_zero.mpr hi)
  apply le_of_tendsto (hc.sub (tendsto_finsetSum (range K) (fun i _ => ht i))).norm
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact tail_right χ hχ hK hs

/-- Ordinary, consecutively ordered harmonic sums converge to the nonzero continued L-value. -/
theorem harmonic_limit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun K => ∑ i ∈ range K, χ (i : ZMod q) / (i:ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction χ 1)) ∧ DirichletCharacter.LFunction χ 1 ≠ 0 := by
  refine ⟨Metric.tendsto_nhds.mpr ?_, DirichletCharacter.LFunction_apply_one_ne_zero hχ⟩
  intro ε hε
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_const_div_atTop_nhds_zero_nat (q:ℝ)).eventually_lt_const hε] with K hK hsmall
  rw [dist_comm,dist_eq_norm]
  exact (harmonic_error χ hχ hK).trans_lt hsmall

#print axioms harmonic_error
#print axioms harmonic_limit
end Arxiv.«2501.03234».ThetaCharacterHarmonicLimit
