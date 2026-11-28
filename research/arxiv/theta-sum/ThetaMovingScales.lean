import ThetaCenteredPrimeBand

/-! Uniform scales for finite, moving deviations of the original prime sum. -/
namespace Arxiv.«2501.03234».ThetaMovingScales
open Real Filter ThetaSmoothConditionalModel ThetaTiltBudget
noncomputable section

private theorem ceil_exp {x : ℝ} (hx : 1≤x) :
    exp x≤(⌈exp x⌉₊:ℝ) ∧ (⌈exp x⌉₊:ℝ)≤exp (2*x) := by
  have he : 2≤exp x := by linarith only [add_one_le_exp x,hx]
  refine ⟨Nat.le_ceil _,?_⟩
  calc _ ≤ exp x+1 := (Nat.ceil_lt_add_one (exp_pos _).le).le
       _ ≤ exp x*exp x := by nlinarith only [he,sq_nonneg (exp x-1)]
       _ = _ := by rw [←exp_add];congr 1;ring

/-- The projection height costs a quadratic deviation in h. The independent
moment order k pays at most exp(8k²h) at the finite endpoint. -/
theorem parameters {D : ℝ} (hD : 0≤D) (U₀ : ℕ) :
    ∀ᶠ h : ℝ in atTop, ∀ k : ℕ, 1≤k → (k:ℝ)≤exp (h/8) →
    ∃ U T : ℕ, U₀≤U ∧ 2≤T ∧
      ThetaModelExponentialMoment.height U≤(952*envelope)*h^2 ∧
      exp ((k:ℝ)*h)≤(T:ℝ) ∧ (T:ℝ)≤exp (2*(k:ℝ)*h) ∧
      (((2*k:ℕ):ℝ)/(tilt U*((2+D)*h^2)))^(2*k)≤exp (-((k:ℝ)*h)/4) ∧
      (D*(T:ℝ)^2/((2+D)*h^2))^(2*k)≤exp (8*(k:ℝ)^2*h) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (U₀:ℝ)] with h hh h₀
  intro k hk hkh
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hp : 0<h := by linarith
  have hkh' : 1≤(k:ℝ)*h := one_le_mul_of_one_le_of_one_le hk' hh
  let U := ⌈exp h⌉₊
  let T := ⌈exp ((k:ℝ)*h)⌉₊
  obtain ⟨hul,huh⟩ := ceil_exp hh
  obtain ⟨htl,hth⟩ := ceil_exp hkh'
  have hU : (U₀:ℝ)≤(U:ℝ) := by linarith only [h₀,add_one_le_exp h,hul]
  have hT : (2:ℝ)≤(T:ℝ) := by linarith only [hkh',add_one_le_exp ((k:ℝ)*h),htl]
  have hlog := log_le_log ((exp_pos h).trans_le hul) huh
  rw [log_exp] at hlog
  have hlog' : 0≤log (U:ℝ) := Real.log_nonneg (by linarith only [hul,add_one_le_exp h,hp])
  have hheight : ThetaModelExponentialMoment.height U≤(952*envelope)*h^2 := by
    unfold ThetaModelExponentialMoment.height
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlog' hlog 2) (by norm_num : (0:ℝ)≤238)) envelope_nonneg).trans_eq (by ring)
  refine ⟨U,T,by exact_mod_cast hU,by exact_mod_cast hT,hheight,htl,?_,?_,?_⟩
  · simpa only [mul_assoc] using hth
  · have ht : exp (h/4)≤tilt U := by
      unfold tilt
      rw [show h/4=h*(1/4:ℝ) by ring,exp_mul]
      exact rpow_le_rpow (exp_pos _).le hul (by norm_num)
    have hu : 2≤(2+D)*h^2 := by
      have H := one_le_pow₀ hh (n:=2)
      nlinarith only [mul_le_mul_of_nonneg_left H (show 0≤2+D by linarith),hD]
    have hv : exp (-(h/8))*tilt U≥exp (h/8) := by
      exact (show exp (h/8)=exp (-(h/8))*exp (h/4) by rw [←exp_add];congr 1;ring).le.trans
        (mul_le_mul_of_nonneg_left ht (exp_pos _).le)
    have hb : ((2*k:ℕ):ℝ)/(tilt U*((2+D)*h^2))≤exp (-(h/8)) := by
      rw [div_le_iff₀ (mul_pos ((exp_pos _).trans_le ht) (by linarith))]
      push_cast
      rw [←mul_assoc]
      exact (mul_le_mul_of_nonneg_left (hkh.trans hv) (by norm_num : (0:ℝ)≤2)).trans
        (by rw [mul_comm 2];exact mul_le_mul_of_nonneg_left hu (by positivity [show 0<tilt U from (exp_pos _).trans_le ht]))
    apply (pow_le_pow_left₀ (by positivity [show 0<tilt U from (exp_pos _).trans_le ht]) hb (2*k)).trans_eq
    rw [←exp_nat_mul]
    congr 1
    push_cast
    ring
  · have hu : D≤(2+D)*h^2 := by
      have H := one_le_pow₀ hh (n:=2)
      nlinarith only [mul_le_mul_of_nonneg_left H (show 0≤2+D by linarith)]
    have hbase : D*(T:ℝ)^2/((2+D)*h^2)≤exp (4*(k:ℝ)*h) := calc
      _ ≤ (T:ℝ)^2 := by rw [div_le_iff₀ (by positivity)];nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg (T:ℝ))]
      _ ≤ (exp (2*((k:ℝ)*h)))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hth _
      _ = _ := by rw [sq,←exp_add];congr 1;ring
    apply (pow_le_pow_left₀ (by positivity) hbase (2*k)).trans_eq
    rw [←exp_nat_mul]
    congr 1
    push_cast
    ring

#print axioms parameters
end
end Arxiv.«2501.03234».ThetaMovingScales
