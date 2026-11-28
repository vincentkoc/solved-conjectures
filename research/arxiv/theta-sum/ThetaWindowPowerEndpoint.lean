import ThetaMixedPowerEndpoint

/-! A finite-interval moment uses the period of each product of rows. -/
namespace Arxiv.«2501.03234».ThetaWindowPowerEndpoint
open Finset ThetaPeriodMeans ThetaRowCorrelations ThetaSmoothConditionalModel
noncomputable section

theorem power_endpoint {Y : ℕ} (f : ℕ → ℕ → ℝ) (X k : ℕ) {B : ℝ} (hB : 0≤B)
    (hf : ∀ d∈Icc 2 Y, OnMod d (f d)) (hb : ∀ d∈Icc 2 Y, ∀ n, |f d n|≤B) :
    (∑ n∈range X,(∑ d∈Icc 2 Y,f d n)^k) ≤
      (X:ℝ)*mean Y.factorial (fun n => (∑ d∈Icc 2 Y,f d n)^k)+2*(B*(Y:ℝ)^2)^k := by
  simpa using ThetaMixedPowerEndpoint.mixed (by decide : 0<1) (Nat.factorial_pos Y)
    (one_dvd Y.factorial) (dvd_refl Y.factorial) (fun _ => (1:ℝ)) (fun _ => rfl)
    (fun _ => by norm_num : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n|≤1) f X k hB hf hb

#print axioms power_endpoint
end
end Arxiv.«2501.03234».ThetaWindowPowerEndpoint
