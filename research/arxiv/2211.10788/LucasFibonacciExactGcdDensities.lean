import HosoyaExactGcdDensityLower

/-! Deciding positivity of the density of each exact index–value gcd on a progression. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Real Topology

private lemma frequency_zero_of_empty {m a d : ℕ}
    (empty : ¬∃ n, 0 < n ∧ n ≡ a [MOD m] ∧ n.gcd (lucasFibonacciSum n)=d) (X : ℕ) :
    sampleFreq (gcdFiber m a d) X=0 := by
  have eq : (Icc 1 X).filter (gcdFiber m a d)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n h
    obtain ⟨bounds,cl,val⟩ := mem_filter.mp h
    exact empty ⟨n,(mem_Icc.mp bounds).1,cl,val⟩
  simp [sampleFreq,sample,eq]

/-- Every exact gcd fiber has a density. The finite test decides strict positivity,
and failure gives density zero. -/
theorem exact_gcd_density_decision {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (a : ℕ) :
    ∃ δ : ℝ, Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ) ∧
      (0 < δ ↔ exactGcdTest m a d=true) ∧ (δ=0 ↔ exactGcdTest m a d=false) := by
  obtain ⟨δ,lim⟩ := exact_fiber_density_exists hm hd a
  refine ⟨δ,lim,?_⟩
  cases result : exactGcdTest m a d with
  | false =>
    have empty := (exactGcdTest_iff hm hd a).not.mp (by simp [result])
    have zero := funext (frequency_zero_of_empty empty)
    have eq : δ=0 := tendsto_nhds_unique lim (by rw [zero]; exact tendsto_const_nhds)
    simp [eq]
  | true =>
    let A := firstSelfMultiple (m.lcm d) (Nat.lcm_pos hm hd)
    obtain ⟨ap,dv,ret⟩ := firstSelfMultiple_spec (Nat.lcm_pos hm hd)
    have ma : m ∣ A := (Nat.dvd_lcm_left ..).trans dv
    have da : d ∣ A := (Nat.dvd_lcm_right ..).trans dv
    obtain ⟨t,cl,val⟩ := (exact_gcd_iff_at_return ap ma da ret a).mp ((exactGcdTest_iff hm hd a).mp result)
    obtain ⟨B,bp,bound⟩ := uniform_exact_fiber_lower
    have low := bound ap ret ma t.isLt cl val lim
    have pA : 0 < (A:ℝ) := by exact_mod_cast ap
    have arg : 1 < (B:ℝ)*A := by
      exact_mod_cast (show 1<B*A from (show 1<B by omega).trans_le (Nat.le_mul_of_pos_right B ap))
    have lp := Real.log_pos arg
    have positive : 0 < δ := lt_of_lt_of_le (by positivity) low
    simp [positive,positive.ne']

#print axioms exact_gcd_density_decision

end Arxiv.«2211.10788».IndexDivisors
