import HosoyaExactGcdPeriodicSieve

/-! Frequency estimates for periodic approximations with errors bounded by large common primes. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

noncomputable def sampleFreq (P : ℕ → Prop) [DecidablePred P] (X : ℕ) : ℝ := (sample P X:ℝ)/X
noncomputable def periodMean (Q : ℕ → Prop) [DecidablePred Q] (D : ℕ) : ℝ := (D.count Q:ℝ)/D

lemma periodic_freq_error {Q : ℕ → Prop} [DecidablePred Q] {D : ℕ} (hd : 0 < D)
    (per : Function.Periodic Q D) {X : ℕ} (hx : 0 < X) :
    |sampleFreq Q X-periodMean Q D| ≤ D/X := by
  have xp : 0 < (X:ℝ) := by exact_mod_cast hx
  have h := periodic_sample_error hd per X
  change |(sample Q X:ℝ)-X*periodMean Q D| ≤ D at h
  have eq : sampleFreq Q X-periodMean Q D=((sample Q X:ℝ)-X*periodMean Q D)/X := by
    unfold sampleFreq
    field_simp
  rw [eq,abs_div,abs_of_pos xp]
  exact div_le_div_of_nonneg_right h xp.le

theorem large_common_frequency_bound {K X : ℕ} (hk : 64 ≤ K) (hx : 0 < X) :
    ((largeCommon K X).card:ℝ)/X ≤ 4/K + (1+8*(K:ℝ)^2)/X := by
  have kp : 0 < (K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have xp : 0 < (X:ℝ) := by exact_mod_cast hx
  have cut : X ≤ (X/K+1)*K := by
    have h := Nat.mod_add_div X K
    have r := Nat.mod_lt X (show 0<K by omega)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (X/K) K]
    omega
  have bound := large_common_tail hk X (X/K+1) K cut
  push_cast at bound
  have trunc : ((X/K:ℕ):ℝ) ≤ (X:ℝ)/K := Nat.cast_div_le
  have h : ((largeCommon K X).card:ℝ) ≤ 4*(X:ℝ)/K+(1+8*(K:ℝ)^2) := by
    have cmp : 13*(X:ℝ)/(6*K)+(X:ℝ)/K ≤ 4*X/K := by
      field_simp
      nlinarith
    linarith
  apply (div_le_iff₀ xp).mpr
  calc _ ≤ _ := h
       _ = _ := by field_simp

/-- Counts sandwiched between a periodic count and that count plus the large-prime
tail have an effective error at every positive X. -/
theorem freq_periodic_approx {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    {K D : ℕ} (hk : 64 ≤ K) (hd : 0 < D) (per : Function.Periodic Q D)
    (counts : ∀ X, sample P X ≤ sample Q X ∧ sample Q X ≤ sample P X+(largeCommon K X).card)
    {X : ℕ} (hx : 0 < X) :
    |sampleFreq P X-periodMean Q D| ≤ 4/K+((D:ℝ)+1+8*K^2)/X := by
  have xp : 0 < (X:ℝ) := by exact_mod_cast hx
  obtain ⟨lo,hi⟩ := counts X
  have l : sampleFreq P X ≤ sampleFreq Q X := by
    apply div_le_div_of_nonneg_right _ xp.le
    exact_mod_cast lo
  have u : sampleFreq Q X ≤ sampleFreq P X+((largeCommon K X).card:ℝ)/X := by
    unfold sampleFreq
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ xp.le
    exact_mod_cast hi
  obtain ⟨low,up⟩ := abs_le.mp (periodic_freq_error hd per hx)
  have tail := large_common_frequency_bound hk hx
  have pos : 0 ≤ 4/(K:ℝ)+(1+8*(K:ℝ)^2)/X := by positivity
  rw [abs_le]
  have spl : ((D:ℝ)+1+8*(K:ℝ)^2)/X=D/X+(1+8*(K:ℝ)^2)/X := by ring
  rw [spl]
  constructor <;> linarith

/-- Arbitrarily accurate periodic approximations give a natural density. -/
theorem exists_density_of_freq_approx (f : ℕ → ℝ)
    (approx : ∀ K : ℕ, 64≤K → ∃ v C : ℝ, 0≤C ∧
      ∀ X : ℕ, 0 < X → |f X-v| ≤ 4/K+C/X) : ∃ δ : ℝ, Tendsto f atTop (𝓝 δ) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε he
  obtain ⟨k,hk⟩ := exists_nat_gt (16/ε)
  let K := max 64 k
  have hk' : (16:ℝ)/ε < K := hk.trans_le (by exact_mod_cast (le_max_right 64 k))
  have kp : 0 < (K:ℝ) := by exact_mod_cast (show 0<K by dsimp [K]; omega)
  have small : 4/(K:ℝ) < ε/4 := by
    have := (div_lt_iff₀ he).mp hk'
    apply (div_lt_iff₀ kp).mpr
    nlinarith
  obtain ⟨v,C,cp,est⟩ := approx K (le_max_left ..)
  obtain ⟨N,hN⟩ := exists_nat_gt (4*C/ε+1)
  have close (i : ℕ) (hi : N ≤ i) : dist (f i) v < ε/2 := by
    have h : 4*C/ε+1 < i := hN.trans_le (by exact_mod_cast hi)
    have ip : 0 < (i:ℝ) := (by positivity : (0:ℝ)≤4*C/ε+1).trans_lt h
    have err : C/i < ε/4 := by
      apply (div_lt_iff₀ ip).mpr
      have b := (div_lt_iff₀ he).mp (by linarith : 4*C/ε < i)
      linarith
    rw [Real.dist_eq]
    exact (est i (by exact_mod_cast ip)).trans_lt (by linarith)
  refine ⟨N,fun i hi j hj => ?_⟩
  have tri := dist_triangle (f i) v (f j)
  rw [dist_comm v] at tri
  linarith [close i hi,close j hj]

theorem exact_fiber_density_exists {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (a : ℕ) :
    ∃ δ : ℝ, Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ) := by
  apply exists_density_of_freq_approx
  intro K hk
  let A := densityReturn m d K
  obtain ⟨pos,ret,mA,dA,cover⟩ := densityReturn_spec hm hd K
  refine ⟨periodMean (finiteFiber A m a d) A,(A:ℝ)+1+8*(K:ℝ)^2,by positivity,?_⟩
  intro X hx
  exact freq_periodic_approx hk pos (finiteFiber_periodic A m a d)
    (fun X => finiteFiber_error ret mA dA hd a K X cover) hx

#print axioms large_common_frequency_bound
#print axioms freq_periodic_approx
#print axioms exact_fiber_density_exists

end Arxiv.«2211.10788».IndexDivisors
