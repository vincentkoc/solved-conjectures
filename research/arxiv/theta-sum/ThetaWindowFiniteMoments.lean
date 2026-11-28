import ThetaWindowPowerEndpoint

/-! Finite moments of reciprocal windows, uniform in the numerator cutoffs. -/
namespace Arxiv.«2501.03234».ThetaWindowFiniteMoments
open Real Finset ThetaPeriodMeans ThetaRowCorrelations ThetaSmoothConditionalModel
open ThetaReciprocalBlocks ThetaIdentityModels ThetaAllWindowMoments
noncomputable section

theorem weighted_bound {d : ℕ} (hd : 1<d) (W : Window) (n : ℕ) :
    |(commonWeight W.weightCutoff d/d)*row d (W.width d) n|≤6*Z := by
  obtain ⟨hw,hu⟩ := commonWeight_bounds W.weightCutoff d
  have hdp : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have h := row_fiber (q:=d) (m:=1) (by omega) (by decide) (by simpa) (Nat.mod_lt n (by omega)) (W.width d)
  have hr : |row d (W.width d) (n%d)| ≤ 3*(harmonic d:ℝ) := by simpa using h
  rw [row_onMod] at hr
  have hrow : |row d (W.width d) n|≤6*d := by
    have hh := harmonic_le_one_add_log d
    have h1 : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
    linarith only [hr,hh,log_le_self (Nat.cast_nonneg d),h1]
  rw [abs_mul,abs_of_nonneg (div_nonneg hw hdp.le)]
  apply (mul_le_mul_of_nonneg_left hrow (div_nonneg hw hdp.le)).trans
  have hh : commonWeight W.weightCutoff d/d*(6*d)=6*commonWeight W.weightCutoff d := by field_simp
  rw [hh]
  exact mul_le_mul_of_nonneg_left hu (by norm_num)

theorem pointwise_power {a : ℝ} (ha : 0<a) (k : ℕ) (x : ℝ) :
    x^k≤((k:ℝ)/a)^k*exp (a*|x|) := by
  have hh := pow_div_factorial_le_exp _ (mul_nonneg ha.le (abs_nonneg x)) k
  rw [div_le_iff₀ (by positivity : 0<(k.factorial:ℝ)),mul_pow] at hh
  have hf : (k.factorial:ℝ)≤(k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  calc x^k ≤ |x|^k := by rw [pow_abs]; exact le_abs_self _
       _ ≤ _ := by
         rw [div_pow,div_mul_eq_mul_div,le_div_iff₀ (pow_pos ha _)]
         nlinarith only [hh,mul_le_mul_of_nonneg_left hf (exp_pos (a*|x|)).le]

/-- The complete moment grows factorially in the exponent; truncation adds
at most two times a fixed multiple of the squared denominator cutoff to that power. -/
theorem finite_moment : ∃ a K : ℝ, 0<a ∧ 0<K ∧ ∀ (Y : ℕ) (W : Window), 2≤Y → ∀ X k : ℕ,
    (∑ n∈range X,(rowModel Y W n)^k) ≤ (X:ℝ)*K*((k:ℝ)/a)^k+2*(6*Z*(Y:ℝ)^2)^k := by
  obtain ⟨a,K,ha,hK,H⟩ := all_bound
  refine ⟨a,K,ha,hK,?_⟩
  intro Y W hY X k
  have hz : 0≤Z := tsum_nonneg (fun _ => by positivity)
  have hp := ThetaWindowPowerEndpoint.power_endpoint (Y:=Y)
    (fun d n => (commonWeight W.weightCutoff d/d)*row d (W.width d) n) X k
    (show 0≤6*Z by positivity) (fun d _ n => congrArg (fun z => commonWeight W.weightCutoff d/d*z) (row_onMod d (W.width d) n))
    (fun d hd => weighted_bound (mem_Icc.mp hd).1 W)
  change (∑ n∈range X,(rowModel Y W n)^k)≤(X:ℝ)*mean Y.factorial (fun n => (rowModel Y W n)^k)+_ at hp
  have hm : mean Y.factorial (fun n => (rowModel Y W n)^k) ≤ ((k:ℝ)/a)^k*K := by
    have h₁ := sum_le_sum (s:=range Y.factorial) (fun n _ => pointwise_power ha k (rowModel Y W n))
    rw [← mul_sum] at h₁
    apply (div_le_div_of_nonneg_right h₁ (Nat.cast_nonneg Y.factorial (α:=ℝ))).trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (H Y W hY) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) ha.le) _)
  exact hp.trans (by linarith only [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg X)])

#print axioms finite_moment
end
end Arxiv.«2501.03234».ThetaWindowFiniteMoments
