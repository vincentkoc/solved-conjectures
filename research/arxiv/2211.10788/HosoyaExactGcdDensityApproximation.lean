import HosoyaExactGcdFrequency

/-! Certified rational approximations to all exact gcd densities. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

def rationalFiberMean (A m a d : ℕ) : ℚ := (A.count (finiteFiber A m a d):ℚ)/A

lemma periodic_freq_tendsto {P : ℕ → Prop} [DecidablePred P] {A : ℕ} (ap : 0 < A)
    (per : Function.Periodic P A) : Tendsto (sampleFreq P) atTop (𝓝 (periodMean P A)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε he
  obtain ⟨N,hn⟩ := exists_nat_gt ((A:ℝ)/ε+1)
  refine ⟨N,fun n hi => ?_⟩
  have h : (A:ℝ)/ε+1 < n := hn.trans_le (by exact_mod_cast hi)
  have pos : 0 < (n:ℝ) := (by positivity : (0:ℝ)≤(A:ℝ)/ε+1).trans_lt h
  rw [Real.dist_eq]
  apply (periodic_freq_error ap per (by exact_mod_cast pos)).trans_lt
  apply (div_lt_iff₀ pos).mpr
  have right := (div_lt_iff₀ he).mp (by linarith : (A:ℝ)/ε<n)
  linarith

/-- The finite test overcounts the exact fiber by at most 4/K in limiting density.
The modulus A can be chosen to suit the calculation. -/
theorem rational_density_interval {m a d K A : ℕ} (hd : 0 < d) (hk : 64 ≤ K) (ap : 0 < A)
    (ret : A ∣ Nat.fib A) (ma : m ∣ A) (da : d ∣ A)
    (cover : ∀ p < K^2, p.Prime → d*p ∣ A) {δ : ℝ}
    (lim : Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ)) :
    (rationalFiberMean A m a d:ℝ)-4/K ≤ δ ∧ δ ≤ (rationalFiberMean A m a d:ℝ) := by
  let Q := finiteFiber A m a d
  let C := (A:ℝ)+1+8*(K:ℝ)^2
  have val : (rationalFiberMean A m a d:ℝ)=periodMean Q A := by
    simp [rationalFiberMean,periodMean,Q]
  rw [val]
  have err := fun (X : ℕ) => finiteFiber_error ret ma da hd a K X cover
  have per := finiteFiber_periodic A m a d
  constructor
  · have l := (tendsto_const_nhds (x:=periodMean Q A-4/K)).sub (tendsto_const_div_atTop_nhds_zero_nat C)
    apply le_of_tendsto_of_tendsto (by simpa only [sub_zero] using l) lim
    filter_upwards [eventually_gt_atTop 0] with X hx
    have est := (abs_le.mp (freq_periodic_approx hk ap per err hx)).1
    change periodMean Q A-4/K-C/X ≤ _
    change -(4/(K:ℝ)+C/X) ≤ sampleFreq (gcdFiber m a d) X-periodMean Q A at est
    linarith
  · apply le_of_tendsto_of_tendsto lim (periodic_freq_tendsto ap per)
    exact Filter.Eventually.of_forall fun X => div_le_div_of_nonneg_right
      (by exact_mod_cast (err X).1) (Nat.cast_nonneg X)

/-- The rational density interval has an explicit finite modulus for every cutoff. -/
theorem effective_density_interval {m a d K : ℕ} (hm : 0 < m) (hd : 0 < d) (hk : 64 ≤ K) {δ : ℝ}
    (lim : Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ)) :
    let u : ℝ := rationalFiberMean (densityReturn m d K) m a d
    u-4/K ≤ δ ∧ δ≤u := by
  obtain ⟨pos,ret,ma,da,cover⟩ := densityReturn_spec hm hd K
  exact rational_density_interval hd hk pos ret ma da cover lim

#print axioms rational_density_interval
#print axioms effective_density_interval

end Arxiv.«2211.10788».IndexDivisors
