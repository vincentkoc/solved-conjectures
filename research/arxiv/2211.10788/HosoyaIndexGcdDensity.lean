import HosoyaPeriodicIndexSieve

/-! Natural density from finite periodic index–value gcd tests and an effective tail. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

noncomputable def commonFreq (X : ℕ) : ℝ := (sample allCommon X:ℝ)/X

noncomputable def sieveMean (K : ℕ) : ℝ :=
  ((sievePeriod K).count (smallCommon K):ℝ)/sievePeriod K

/-- The finite-prime density approximates the observed frequency. Both the
prime cutoff K and the cofactor cutoff T can be held fixed while X grows. -/
theorem approx_common_frequency {K T X : ℕ} (hk : 64 ≤ K) (ht : 0 < T) (hx : 0 < X) :
    |commonFreq X-sieveMean K| ≤ 13/(6*(K:ℝ))+1/T+((sievePeriod K:ℝ)+1+8*T^2)/X := by
  let D := sievePeriod K
  have per := periodic_sample_error (Nat.factorial_pos _) (small_periodic K) X
  change |(sample (smallCommon K) X:ℝ)-X*sieveMean K| ≤ D at per
  obtain ⟨pl,pr⟩ := abs_le.mp per
  obtain ⟨sl,su⟩ := small_error K X
  have sl' : (sample (smallCommon K) X:ℝ) ≤ sample allCommon X := by exact_mod_cast sl
  have su' : (sample allCommon X:ℝ) ≤ sample (smallCommon K) X+(largeCommon K X).card := by exact_mod_cast su
  have cut : X ≤ (X/T+1)*T := by
    have d := Nat.mod_add_div X T
    have r := Nat.mod_lt X ht
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (X/T) T]
    omega
  have tail := large_common_tail hk X (X/T+1) T cut
  push_cast at tail
  have trunc : ((X/T:ℕ):ℝ) ≤ (X:ℝ)/T := Nat.cast_div_le
  have xp : (0:ℝ) < X := by exact_mod_cast hx
  have tp : (0:ℝ) < T := by exact_mod_cast ht
  have kp : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have lo : 0 ≤ 13/(6*(K:ℝ))+1/T := by positivity
  have low : 0 ≤ (13/(6*(K:ℝ))+1/T)*X := mul_nonneg lo xp.le
  have shift : ((sievePeriod K:ℝ)+1+8*T^2)/X*X=(D:ℝ)+1+8*T^2 := by dsimp [D]; field_simp
  unfold commonFreq
  apply abs_le.mpr
  constructor
  · rw [le_sub_iff_add_le,le_div_iff₀ xp]
    dsimp [D] at *
    nlinarith [show 0 ≤ (8:ℝ)*T^2 by positivity, shift]
  · rw [sub_le_iff_le_add,div_le_iff₀ xp]
    dsimp [D] at *
    linarith only [pr,su',tail,trunc,shift,
      show (13/(6*(K:ℝ))+1/T+((sievePeriod K:ℝ)+1+8*T^2)/X+sieveMean K)*X=
        13*X/(6*(K:ℝ))+(X:ℝ)/T+((sievePeriod K:ℝ)+1+8*T^2)/X*X+X*sieveMean K by ring]

/-- The proportion of positive indices sharing any prime with their upper
value has a limit. The finite sieves above give approximations to that limit. -/
theorem common_frequency_converges : ∃ δ : ℝ, Tendsto commonFreq atTop (𝓝 δ) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε he
  obtain ⟨k,hk⟩ := exists_nat_gt (32/ε)
  let K := max 64 k
  have hk64 : 64 ≤ K := le_max_left ..
  have kp : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hk' : (32:ℝ)/ε < K := hk.trans_le (by exact_mod_cast (le_max_right 64 k))
  have small : 13/(6*(K:ℝ))+1/K < ε/4 := by
    have raw := (div_lt_iff₀ he).mp hk'
    field_simp
    nlinarith
  let C := (sievePeriod K:ℝ)+1+8*K^2
  obtain ⟨N,hN⟩ := exists_nat_gt (4*C/ε+1)
  have close (i : ℕ) (hi : N ≤ i) : dist (commonFreq i) (sieveMean K) < ε/2 := by
    have h : 4*C/ε+1 < i := hN.trans_le (by exact_mod_cast hi)
    have cp : 0 ≤ C := by dsimp [C]; positivity
    have ip : (0:ℝ) < i := (by positivity : (0:ℝ) ≤ 4*C/ε+1).trans_lt h
    have err : C/i < ε/4 := by
      apply (div_lt_iff₀ ip).mpr
      have b := (div_lt_iff₀ he).mp (by linarith : 4*C/ε < i)
      linarith
    rw [Real.dist_eq]
    exact (approx_common_frequency (T:=K) hk64 (by omega) (by exact_mod_cast ip)).trans_lt
      (by change 13/(6*(K:ℝ))+1/K+C/i < ε/2; linarith)
  refine ⟨N,fun i hi j hj => ?_⟩
  have tri := dist_triangle (commonFreq i) (sieveMean K) (commonFreq j)
  rw [dist_comm (sieveMean K)] at tri
  linarith [close i hi,close j hj]

#print axioms approx_common_frequency
#print axioms common_frequency_converges

end Arxiv.«2211.10788».IndexDivisors
