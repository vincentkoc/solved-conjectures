import HosoyaDivisorWindowCounts
import HosoyaPrimeHarmonicBounds

/-! Transferring a density of divisor primes to a mean number of distinct factors in every window. -/

namespace Arxiv.«2211.10788».DivisorWindows
open Finset Filter
open scoped Topology

private lemma abel_lower (f : ℕ → ℝ) (K : ℝ)
    (h : ∀ n, 0 ≤ (∑ j ∈ range n, f j) + K) (n : ℕ) :
    0 ≤ (∑ j ∈ range n, f j/(j+1)) + K := by
  have step (m : ℕ) : ((∑ j ∈ range m, f j)+K)/(m+1) ≤
      (∑ j ∈ range m, f j/(j+1))+K := by
    induction m with
    | zero => simp
    | succ m ih =>
      have mono : ((∑ j ∈ range (m+1), f j)+K)/((m:ℝ)+2) ≤
          ((∑ j ∈ range (m+1), f j)+K)/((m:ℝ)+1) :=
        div_le_div_of_nonneg_left (h _) (by positivity) (by linarith)
      rw [sum_range_succ] at mono ⊢
      push_cast
      rw [show (m:ℝ)+1+1=m+2 by ring]
      apply mono.trans
      rw [show (∑ j ∈ range m, f j)+f m+K=(∑ j ∈ range m, f j)+K+f m by ring,add_div]
      rw [sum_range_succ]
      linarith
  exact (div_nonneg (h _) (by positivity)).trans (step n)

private lemma count_as_sum (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    (Nat.count P n:ℝ)=∑ j ∈ range n, if P j then (1:ℝ) else 0 := by
  rw [Nat.count_eq_card_filter_range,card_filter,Nat.cast_sum]
  apply sum_congr rfl; intro i _; split_ifs <;> norm_num

private lemma weight_lower (A : ℕ → Prop) [DecidablePred A] (c K : ℝ)
    (h : ∀ n, c*(Nat.count Nat.Prime n:ℝ) ≤ (Nat.count A n:ℝ)+K) (n : ℕ) :
    c*(∑ p ∈ n.primesBelow, 1/((p:ℝ)+1)) ≤ (∑ p ∈ (range n).filter A, 1/((p:ℝ)+1))+K := by
  let f (p : ℕ) := (if A p then (1:ℝ) else 0)-c*(if p.Prime then 1 else 0)
  have nonneg (i : ℕ) : 0≤(∑ j ∈ range i, f j)+K := by
    simp only [f,sum_sub_distrib,←mul_sum,←count_as_sum]
    linarith [h i]
  have hsum := abel_lower f K nonneg n
  have term (p : ℕ) : f p/(p+1) =
      (if A p then 1/((p:ℝ)+1) else 0)-c*(if p.Prime then 1/((p:ℝ)+1) else 0) := by
    by_cases hA : A p <;> by_cases hP : p.Prime <;> simp [f,hA,hP,div_eq_mul_inv,sub_mul]
  simp only [term,sum_sub_distrib,←mul_sum,←sum_filter] at hsum
  rw [Nat.primesBelow_eq_filter_range]
  linarith

/-- Divisor primes below x on the chosen index progression. -/
noncomputable def divisorPrimes (r d x : ℕ) : Finset ℕ := by
  classical exact (range x).filter (Hits r d)

/-- A finite unconditional bound in terms of the reciprocal mass of divisor primes
through H, valid for any start and step (including a constant progression). -/
theorem window_harmonic_bound (r d a H : ℕ) (hH : 0<H) :
    (∑ p ∈ divisorPrimes r d (H+1), 1/((p:ℝ)+1)) ≤
      (∑ i ∈ range H, ((lucasFibonacciSum (r+d*(a+i))).primeFactors.card:ℝ))/H + 2 := by
  classical
  let S := (range (H+1)).filter (Hits r d)
  have hit := factor_incidences (r:=r) (d:=d) S (fun p h => (mem_filter.mp h).2) a H
  have wt (p : ℕ) : (H:ℝ)*(1/((p:ℝ)+1)) ≤ ((H/(p+1):ℕ):ℝ)+1 := by
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    have := (Nat.lt_mul_div_succ H (by omega : 0<p+1)).le
    rw [Nat.mul_comm] at this
    exact_mod_cast this
  have le := sum_le_sum (s:=S) (fun p _ => wt p)
  rw [←mul_sum,sum_add_distrib] at le
  simp only [sum_const,nsmul_eq_mul,mul_one] at le
  have hc : S.card≤H+1 := (card_le_card (filter_subset ..)).trans (by simp)
  have H0 : (0:ℝ)<H := by exact_mod_cast hH
  change (∑ p ∈ S, 1/((p:ℝ)+1)) ≤ _
  have realHit : (∑ p ∈ S, ((H/(p+1):ℕ):ℝ)) ≤
      ∑ i ∈ range H, ((lucasFibonacciSum (r+d*(a+i))).primeFactors.card:ℝ) := by exact_mod_cast hit
  have realCard : (S.card:ℝ) ≤ H+1 := by exact_mod_cast hc
  have oneH : (1:ℝ)≤H := by exact_mod_cast hH
  rw [show (∑ i ∈ range H, ((lucasFibonacciSum (r+d*(a+i))).primeFactors.card:ℝ))/H+2=
      ((∑ i ∈ range H, ((lucasFibonacciSum (r+d*(a+i))).primeFactors.card:ℝ))+2*H)/H by
        field_simp]
  apply (le_div_iff₀ H0).mpr
  rw [mul_comm]
  linarith

/-- A lower bound c for the relative frequency of divisor primes, valid eventually,
forces a uniform mean of at least c log log(H+1) up to an additive constant. -/
theorem mean_factors_of_divisor_prime_counts {r d : ℕ} {c : ℝ} (hc : 0≤c)
    (hd : ∀ᶠ n : ℕ in atTop, c*n.primesBelow.card ≤ ((divisorPrimes r d n).card:ℝ)) :
    ∃ C : ℝ, ∀ (H : ℕ), 1≤H → ∀ a : ℕ, c*Real.log (Real.log (H+1)) ≤
      (∑ i ∈ range H, ((lucasFibonacciSum (r+d*(a+i))).primeFactors.card:ℝ))/H + C := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hd
  let K : ℝ := c*N
  have hK : 0≤K := mul_nonneg hc (Nat.cast_nonneg _)
  have support (n : ℕ) : c*(Nat.count Nat.Prime n:ℝ) ≤ (Nat.count (Hits r d) n:ℝ)+K := by
    rw [Nat.count_eq_card_filter_range,Nat.count_eq_card_filter_range,←Nat.primesBelow_eq_filter_range]
    by_cases hn : N≤n
    · exact (hN _ hn).trans (le_add_of_nonneg_right hK)
    · have le : n.primesBelow.card ≤ N := (card_le_card (s:=n.primesBelow) (t:=range n)
        (fun i h => mem_range.mpr (Nat.lt_of_mem_primesBelow h))).trans (by simp; omega)
      have := mul_le_mul_of_nonneg_left (show (n.primesBelow.card:ℝ) ≤ N by exact_mod_cast le) hc
      exact this.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  refine ⟨K+2+2*c,?_⟩
  intro H hH a
  have logbound := mul_le_mul_of_nonneg_left (log_log_le_prime_weight hH) hc
  have transfer := weight_lower (Hits r d) c K support (H+1)
  have finite := window_harmonic_bound r d a H hH
  change (∑ p ∈ (range (H+1)).filter (Hits r d), 1/((p:ℝ)+1)) ≤ _ at finite
  linarith

/-- If the divisor primes on a progression have positive relative density δ,
then every coefficient below δ works in a log-log mean lower bound uniformly
over all translated windows of sufficiently large length. -/
theorem every_window_of_relative_density {r d : ℕ} {c δ : ℝ} (hc : 0≤c) (hlt : c<δ)
    (hδ : Tendsto (fun n : ℕ => ((divisorPrimes r d n).card:ℝ)/n.primesBelow.card) atTop (𝓝 δ)) :
    ∀ᶠ H : ℕ in atTop, ∀ a : ℕ, c*Real.log (Real.log ((H:ℝ)+1)) ≤
      (∑ i ∈ range H, ((lucasFibonacciSum (r+d*(a+i))).primeFactors.card:ℝ))/H := by
  let g := (c+δ)/2
  have cg : c<g := by dsimp [g]; linarith
  have gd : g<δ := by dsimp [g]; linarith
  have counts : ∀ᶠ n : ℕ in atTop, g*n.primesBelow.card ≤ ((divisorPrimes r d n).card:ℝ) := by
    filter_upwards [hδ.eventually (lt_mem_nhds gd),eventually_ge_atTop 3] with n h hn
    have hp : 2 ∈ n.primesBelow := Nat.mem_primesBelow.mpr ⟨by omega,by decide⟩
    have pos : (0:ℝ)<n.primesBelow.card := by exact_mod_cast card_pos.mpr ⟨2,hp⟩
    exact ((lt_div_iff₀ pos).mp h).le
  obtain ⟨C,bound⟩ := mean_factors_of_divisor_prime_counts (hc.trans cg.le) counts
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have grow := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp ht)
  filter_upwards [grow.eventually_ge_atTop (C/(g-c)),eventually_ge_atTop 1] with H h Hpos
  intro a
  have gap := (div_le_iff₀ (sub_pos.mpr cg)).mp h
  simp only [Function.comp_apply] at gap
  nlinarith only [gap,bound H Hpos a]

#print axioms every_window_of_relative_density

#print axioms window_harmonic_bound
#print axioms mean_factors_of_divisor_prime_counts

end Arxiv.«2211.10788».DivisorWindows
