import HosoyaMobiusDivisorSieve
import HosoyaRankLcmSummability

/-! An absolutely convergent series for every exact index–upper-value gcd density. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius

private lemma divisorSieve_error {m a d B K : ℕ} (hd : 0 < d)
    (cover : ∀ p < K^2, p.Prime → p ∣ B) (X : ℕ) :
    sample (gcdFiber m a d) X ≤ sample (divisorSieve m a d B) X ∧
    sample (divisorSieve m a d B) X ≤ sample (gcdFiber m a d) X+(largeCommon K X).card := by
  constructor
  · apply card_le_card
    intro n hn
    obtain ⟨bounds,cl,val⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨bounds,cl,by simp [val],by simp [val,Nat.div_self hd]⟩
  have sub : (Icc 1 X).filter (divisorSieve m a d B) ⊆
      (Icc 1 X).filter (gcdFiber m a d) ∪ largeCommon K X := by
    intro n hn
    obtain ⟨bounds,cl,dv,cp⟩ := mem_filter.mp hn
    obtain ⟨t,eq⟩ := dv
    by_cases one : t=1
    · exact mem_union_left _ (mem_filter.mpr ⟨bounds,cl,by simpa [one] using eq⟩)
    obtain ⟨p,pr,pt⟩ := Nat.exists_prime_and_dvd one
    have pc : p ∣ n.gcd (lucasFibonacciSum n) := eq ▸ pt.trans (dvd_mul_left t d)
    have cop : t.Coprime B := by simpa only [eq,Nat.mul_div_cancel_left _ hd] using cp
    have big : K^2≤p := by
      by_contra! small
      exact pr.not_dvd_one (cop ▸ Nat.dvd_gcd pt (cover p small pr))
    exact mem_union_right _ (mem_filter.mpr ⟨bounds,p,pr.mem_primeFactors (pc.trans (Nat.gcd_dvd_left ..))
      (by have lo := (mem_Icc.mp bounds).1; omega),big,pc.trans (Nat.gcd_dvd_right ..)⟩)
  exact (card_le_card sub).trans (card_union_le ..)

/-- In a finite inclusion-exclusion it suffices to cover each small prime once. -/
theorem divisorSum_interval {m a d B K : ℕ} (hm : 0 < m) (hd : 0 < d) (hb : 0 < B)
    (hk : 64≤K) (cover : ∀ p < K^2, p.Prime → p ∣ B) {δ : ℝ}
    (lim : Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ)) :
    divisorSum m a d B-4/K ≤ δ ∧ δ ≤ divisorSum m a d B := by
  have approx := divisorSieve_limit (a:=a) hm hd hb
  have err := divisorSieve_error (m:=m) (a:=a) hd cover
  constructor
  · have upper := (approx.sub (tendsto_const_nhds (x:=(4:ℝ)/K))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1+8*(K:ℝ)^2))
    apply le_of_tendsto_of_tendsto (by simpa only [sub_zero] using upper) lim
    filter_upwards [eventually_gt_atTop 0] with X hx
    have cmp := div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (err X).2) (Nat.cast_nonneg (α:=ℝ) X)
    rw [Nat.cast_add,add_div] at cmp
    have tail := large_common_frequency_bound hk hx
    change sampleFreq (divisorSieve m a d B) X-4/K-(1+8*(K:ℝ)^2)/X ≤ _
    unfold sampleFreq
    linarith
  · apply le_of_tendsto_of_tendsto lim approx
    exact Eventually.of_forall fun X => div_le_div_of_nonneg_right
      (by exact_mod_cast (err X).1) (Nat.cast_nonneg X)

noncomputable def mobiusTerm (m a d j : ℕ) : ℝ := (μ j:ℝ)*intersectionMass m a (d*j)

/-- Uniform absolute majorant, independent of the target gcd and progression. -/
theorem mobiusTerm_abs_le {m a d : ℕ} (hm : 0 < m) (hd : 0 < d) (j : ℕ) :
    |mobiusTerm m a d j| ≤ lcmWeight j := by
  by_cases zero : j=0
  · simp [zero,mobiusTerm,lcmWeight,rankLcm]
  have jp := Nat.pos_of_ne_zero zero
  have dj := Nat.mul_pos hd jp
  have hdiv : rankLcm j ∣ jointPeriod m (d*j) :=
    (rankLcm_mono_dvd jp dj (dvd_mul_left j d)).trans (Nat.dvd_lcm_right ..)
  have lo := Nat.le_of_dvd (jointPeriod_pos hm dj) hdiv
  have pos : 0 < rankLcm j := Nat.lcm_pos jp (rank_pos_all jp)
  have mu : |(μ j:ℝ)|≤1 := by
    rcases moebius_eq_or j with h|h|h <;> simp [h]
  have inv : (jointPeriod m (d*j):ℝ)⁻¹ ≤ lcmWeight j :=
    inv_anti₀ (by exact_mod_cast pos) (by exact_mod_cast lo)
  rw [mobiusTerm,abs_mul,intersectionMass_eq dj]
  split
  · rw [one_div,abs_of_nonneg (show 0≤(jointPeriod m (d*j):ℝ)⁻¹ by positivity)]
    exact (mul_le_of_le_one_left (by positivity) mu).trans inv
  · simp [lcmWeight]

theorem mobiusTerm_summable {m a d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    Summable (fun j => |mobiusTerm m a d j|) :=
  rankLcm_summable.of_nonneg_of_le (fun _ => abs_nonneg _) (mobiusTerm_abs_le hm hd)

private lemma factorialDivisors_tendsto :
    Tendsto (fun K : ℕ => insert 0 (K^2).factorial.divisors) atTop atTop := by
  apply tendsto_atTop.mpr
  intro S
  filter_upwards [eventually_ge_atTop (S.sup id+1)] with K large
  intro j hj
  by_cases zero : j=0
  · simp [zero]
  apply mem_insert_of_mem
  apply Nat.mem_divisors.mpr
  have le : j ≤ S.sup id := le_sup (f:=id) hj
  have square : K≤K^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right K (show 0<K by omega)
  exact ⟨Nat.dvd_factorial (Nat.pos_of_ne_zero zero) (by omega),Nat.factorial_ne_zero _⟩

/-- For positive m,d the exact gcd frequency on n ≡ a (mod m) tends to the
Möbius series. Each coefficient is specified by `intersectionMass_eq`. -/
theorem exact_gcd_mobius_density {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (a : ℕ) :
    Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 (∑' j, mobiusTerm m a d j)) := by
  obtain ⟨δ,lim⟩ := exact_fiber_density_exists hm hd a
  have series := (mobiusTerm_summable (a:=a) hm hd).of_abs.hasSum
  have finiteLim : Tendsto (fun K : ℕ => divisorSum m a d (K^2).factorial) atTop
      (𝓝 (∑' j, mobiusTerm m a d j)) := by
    have comp := series.comp factorialDivisors_tendsto
    apply comp.congr'
    filter_upwards with K
    change ∑ j ∈ insert 0 (K^2).factorial.divisors, mobiusTerm m a d j=_
    rw [sum_insert (by simp)]
    simp [divisorSum,mobiusTerm]
  have bounds : ∀ᶠ K : ℕ in atTop, divisorSum m a d (K^2).factorial-4/K≤δ ∧
      δ≤divisorSum m a d (K^2).factorial := by
    filter_upwards [eventually_ge_atTop 64] with K hk
    exact divisorSum_interval hm hd (Nat.factorial_pos _) hk
      (fun p small pr => Nat.dvd_factorial pr.pos small.le) lim
  have adj := finiteLim.sub (tendsto_const_div_atTop_nhds_zero_nat (4:ℝ))
  rw [sub_zero] at adj
  have left := le_of_tendsto adj (bounds.mono fun _ h => h.1)
  have right := ge_of_tendsto finiteLim (bounds.mono fun _ h => h.2)
  rwa [le_antisymm left right]

#print axioms divisorSum_interval
#print axioms mobiusTerm_abs_le
#print axioms mobiusTerm_summable
#print axioms exact_gcd_mobius_density

end Arxiv.«2211.10788».IndexDivisors
