import ThetaIdentityModulus

/-! Uniform denominator control for a prescribed growing family of moduli. -/
namespace Arxiv.«2501.03234».ThetaFactorialSequence
open Finset Filter ThetaDivisorLogMean ThetaFactorialRows ThetaSmoothRows ThetaIdentityModulus
open scoped Topology
noncomputable section

def modulus (t : ℕ) := t.factorial^t

private theorem small_decay :
    Tendsto (fun t : ℕ => (t:ℝ)*(L t + t*Real.log t)/(2:ℝ)^t) atTop (𝓝 0) := by
  have h3 := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1:ℝ)<2)
  have hu := h3.const_mul 6
  rw [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with t ht
    have hl := Real.log_nonneg (by exact_mod_cast ht : (1:ℝ)≤ t)
    unfold L; positivity
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with t ht
    have ht' : (1:ℝ)≤ t := by exact_mod_cast ht
    have hl := Real.log_nonneg ht'
    have hb := Real.log_le_self (Nat.cast_nonneg t)
    change (t:ℝ)*(L t+t*Real.log t)/2^t≤6*((t:ℝ)^3/2^t)
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    unfold L
    have h₂ : Real.log t*(1+Real.log t)≤(t:ℝ)*(1+t) :=
      mul_le_mul hb (by linarith) (by linarith) (Nat.cast_nonneg _)
    have h₃ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg t)
    nlinarith [mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg t),
      mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg t),
      mul_nonneg (sub_nonneg.mpr ht') (sq_nonneg (t:ℝ)),
      mul_nonneg (sub_nonneg.mpr ht') (Nat.cast_nonneg t)]

/-- With exponent equal to the factorial cutoff, the absolute error of all
omitted denominators is an arbitrarily small fraction of divisor mass. -/
theorem little (C : ℝ) (hC : 0≤ C) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (D : Finset ℕ), (∀ d∈D,0< d ∧ d≤ Y ∧ ¬d∣modulus T) →
      C*∑ d∈D,logWeight ((modulus T).gcd d)*tailWeight (d/((modulus T).gcd d)) ≤ ε*mass (modulus T) := by
  have hdec := (smooth_decay.add small_decay).mul_const (C*zetaBound)
  rw [zero_add,zero_mul] at hdec
  filter_upwards [eventually_ge_atTop (1:ℕ),hdec.eventually_le_const he] with T hT H
  intro Y D hD
  let m := modulus T
  have hm : 0 < m := pow_pos (Nat.factorial_pos _) _
  have hlog := smooth hm (fun p hp => factorial_smooth hp)
  change logMass m≤ mass m*L T at hlog
  have hz : 0≤ zetaBound := tsum_nonneg fun _ => by positivity
  have hm' := mass_nonneg m
  have h := omitted hT D hD
  apply (mul_le_mul_of_nonneg_left h hC).trans
  have hu : logMass m*(zetaBound/(T:ℝ)^(1/16:ℝ))+
      (T*((logMass m+T*Real.log T*mass m)/(2:ℝ)^T))*zetaBound ≤
      (mass m*L T)*(zetaBound/(T:ℝ)^(1/16:ℝ))+
      (T*((mass m*L T+T*Real.log T*mass m)/(2:ℝ)^T))*zetaBound := by gcongr
  apply (mul_le_mul_of_nonneg_left hu hC).trans
  calc _ = ((L T/(T:ℝ)^(1/16:ℝ)+(T:ℝ)*(L T+T*Real.log T)/(2:ℝ)^T)*(C*zetaBound))*mass m := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right H hm'
#print axioms little
end
end Arxiv.«2501.03234».ThetaFactorialSequence
