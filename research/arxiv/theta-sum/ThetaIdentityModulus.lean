import ThetaFactorialRows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Choice of a factorial progression with arbitrarily large captured mass. -/
namespace Arxiv.«2501.03234».ThetaIdentityModulus
open Finset Filter ThetaDivisorLogMean ThetaFactorialRows ThetaSmoothRows
open scoped Topology
noncomputable section

def L (T : ℕ) : ℝ := 1+2*Real.log T*(1+Real.log T)

theorem smooth_decay : Tendsto (fun T : ℕ => L T/(T:ℝ)^(1/16:ℝ)) atTop (𝓝 0) := by
  let u (T : ℕ) : ℝ := (T:ℝ)^(1/16:ℝ)
  have hu : Tendsto u atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun T : ℕ => 1/u T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hu
  have h1 : Tendsto (fun T : ℕ => Real.log T/u T) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/16)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun T : ℕ => Real.log T^2/u T) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two,u] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/16)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  convert h0.add ((h1.add h2).const_mul 2) using 1
  · ext T; dsimp [L,u]; ring
  · ring

private theorem exponential_decay (T : ℕ) :
    Tendsto (fun A : ℕ => (L T + A*Real.log T)/(2:ℝ)^A) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  simp only [pow_zero,pow_one] at h0 h1
  convert (h0.const_mul (L T)).add (h1.mul_const (Real.log T)) using 1
  · ext A; ring
  · ring

theorem choose (B C : ℝ) (hC : 0≤ C) : ∃ T A : ℕ, 2≤ T ∧ 0< A ∧
    let m := T.factorial^A
    B≤ mass m ∧ ∀ (Y : ℕ) (D : Finset ℕ), (∀ d∈D,0< d ∧ d≤ Y ∧ ¬d∣m) →
      C*∑ d∈D,logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤ mass m/8 := by
  have hz : 0≤ zetaBound := tsum_nonneg fun _ => by positivity
  have hdec := smooth_decay.mul_const (C*zetaBound)
  rw [zero_mul] at hdec
  have hh : Tendsto (fun T : ℕ => Real.log (T:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT,hl,hb⟩ := ((eventually_ge_atTop (2:ℕ)).and ((hdec.eventually_le_const (by norm_num : (0:ℝ)<1/16)).and
    (hh.eventually_ge_atTop B))).exists
  have hdecA := (exponential_decay T).mul_const ((T:ℝ)*C*zetaBound)
  rw [zero_mul] at hdecA
  obtain ⟨A,hA,ha⟩ := ((eventually_ge_atTop (1:ℕ)).and (hdecA.eventually_le_const (by norm_num : (0:ℝ)<1/16))).exists
  let m := T.factorial^A
  have hm : 0 < m := pow_pos (Nat.factorial_pos _) _
  have hD := mass_nonneg m
  have hs : logMass m≤ mass m*L T := smooth hm (fun p hp => factorial_smooth hp)
  refine ⟨T,A,hT,hA,?_,?_⟩
  · exact hb.trans ((Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ T)).trans ((log_add_one_le_harmonic T).trans (factorial_mass hA)))
  · intro Y D h
    have H := omitted (by omega : 0< T) D h
    have hlog : 0≤ Real.log T := Real.log_nonneg (by exact_mod_cast (by omega : 1≤ T))
    have hbig : logMass m*(zetaBound/(T:ℝ)^(1/16:ℝ)) ≤ (mass m*L T)*(zetaBound/(T:ℝ)^(1/16:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    have hsmall : (T*((logMass m+A*Real.log T*mass m)/(2:ℝ)^A))*zetaBound ≤
        (T*((mass m*L T+A*Real.log T*mass m)/(2:ℝ)^A))*zetaBound := by gcongr
    apply (mul_le_mul_of_nonneg_left H hC).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hbig hsmall) hC).trans
    have hl' := mul_le_mul_of_nonneg_left hl hD
    have ha' := mul_le_mul_of_nonneg_left ha hD
    calc _ = mass m*((L T/(T:ℝ)^(1/16:ℝ))*(C*zetaBound))+
                 mass m*((L T+A*Real.log T)/(2:ℝ)^A*((T:ℝ)*C*zetaBound)) := by ring
         _ ≤ mass m*(1/16)+mass m*(1/16) := add_le_add hl' ha'
         _ = _ := by ring

#print axioms choose
end
end Arxiv.«2501.03234».ThetaIdentityModulus
