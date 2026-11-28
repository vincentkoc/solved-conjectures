import ThetaCompactOmitted

/-! The omitted divisor envelope is uniformly o(mass) for the compact modulus. -/
namespace Arxiv.«2501.03234».ThetaCompactSequence
open Finset Real Filter ThetaDivisorLogMean ThetaFactorialRows ThetaSmoothRows ThetaIdentityModulus
open ThetaCompactModulus
noncomputable section

theorem little (C : ℝ) (hC : 0≤C) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (D : Finset ℕ), (∀ d∈D,0 < d ∧ d≤Y ∧ ¬d∣modulus T) →
      C*∑ d∈D,logWeight ((modulus T).gcd d)*tailWeight (d/((modulus T).gcd d)) ≤ ε*mass (modulus T) := by
  have hdec := smooth_decay.mul_const (6*C*zetaBound)
  rw [zero_mul] at hdec
  filter_upwards [eventually_ge_atTop (1:ℕ),hdec.eventually_le_const he] with T ht hlim
  intro Y D hD
  let m := modulus T
  have hm := positive T
  have hL : logMass m≤ mass m*L T := ThetaDivisorLogMean.smooth hm (fun _ h => ThetaCompactModulus.smooth h)
  have hl := log_nonneg_nat T
  have hlt : log T≤L T := by unfold L; nlinarith only [hl,sq_nonneg (log (T:ℝ))]
  have hL0 : 0≤L T := hl.trans hlt
  have hm0 := mass_nonneg m
  have h1 : (1:ℝ)≤T := by exact_mod_cast ht
  have hT : 0<(T:ℝ) := by linarith
  let t := (T:ℝ)^(1/16:ℝ)
  have ht0 : 0<t := rpow_pos_of_pos hT _
  have htT : t≤T := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h1 (by norm_num : (1/16:ℝ)≤1)
  have htop : logMass m+4*log T*mass m≤5*(mass m*L T) := by
    nlinarith only [hL,mul_le_mul_of_nonneg_left hlt hm0]
  have hsm : (logMass m+4*log T*mass m)/T≤5*(mass m*L T)/t :=
    (div_le_div_of_nonneg_right htop hT.le).trans (div_le_div_of_nonneg_left (by positivity) ht0 htT)
  have hz : 0≤zetaBound := tsum_nonneg fun _ => by positivity
  have H := ThetaCompactOmitted.omitted ht D hD
  apply (mul_le_mul_of_nonneg_left H hC).trans
  have htot := add_le_add (mul_le_mul_of_nonneg_right hL (show 0≤zetaBound/t by positivity))
    (mul_le_mul_of_nonneg_right hsm hz)
  apply (mul_le_mul_of_nonneg_left htot hC).trans
  change C*(mass m*L T*(zetaBound/t)+(5*(mass m*L T)/t)*zetaBound)≤ε*mass m
  have HH := mul_le_mul_of_nonneg_right hlim hm0
  change (L T/t)*(6*C*zetaBound)*mass m≤_ at HH
  convert HH using 1
  ring

#print axioms little
end
end Arxiv.«2501.03234».ThetaCompactSequence
