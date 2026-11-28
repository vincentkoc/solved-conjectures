import ThetaConductorMoment
import ThetaTotientTail
import ThetaFullVarianceTail

/-! Uniform inverse-conductor cutoff for the variance of the prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaInverseConductorTail
noncomputable section
open Finset Filter Topology ThetaLevelCoefficients ThetaNaturalPrimeMeans
open ThetaSpectralVariance ThetaFullVarianceTail ThetaFiniteProjection

/-- The total variance omitted at conductor Y is O(1/Y), including small positive cutoffs. -/
theorem truncation {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) (Y : ℕ) (hY : 0<Y) :
    ∑ u∈through Y,u.mass ≤ V ∧ V ≤ ∑ u∈through Y,u.mass + 449280/Y := by
  have hH : ThetaLValueMoment.H^3≤64 :=
    (pow_le_pow_left₀ (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) ThetaLValueMoment.H_bound 3).trans_eq (by norm_num)
  apply cutoff_of_majorant hV hAP Y (fun q => 74880*(1/((q:ℝ)*q.totient)))
  · intro q hq t ht
    apply (ThetaConductorMoment.level t (by omega) ht hAP).trans
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · intro c hc
    rw [←mul_sum]
    calc _ ≤ 74880*(6/(Y:ℝ)) := mul_le_mul_of_nonneg_left
                 (ThetaTotientTail.bound Y hY c (fun n hn => (hc n hn).le)) (by norm_num)
         _ = _ := by ring

/-- The full cutoff estimate applies to the optimal projection at any modulus
containing all odd conductors through the cutoff. -/
theorem period_bound {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] (Y : ℕ) (hY : 0<Y)
    (hm : ∀ q≤Y,Odd q → q∣m) : V-energy m ≤ 449280/Y := by
  classical
  let s := (through Y).filter (fun u => Odd u.modulus)
  have he : ∑ u∈through Y,u.mass=∑ u∈s,u.mass := by
    apply (sum_subset (filter_subset ..) ?_).symm
    intro u hu hf
    have hn : ¬Odd u.character.conductor := by
      intro h
      exact hf (mem_filter.mpr ⟨hu,(show u.character.conductor=u.modulus from u.primitive) ▸ h⟩)
    simp [Mode.mass,value,hn]
  have hsub : s⊆modesAt m := by
    intro u hu
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hu
    exact (mem_modesAt u).mpr (hm _ ((mem_through u Y).mp h₁) h₂)
  have hs := (sum_le_sum_of_subset_of_nonneg (f:=Mode.mass) hsub (fun u _ _ => sq_nonneg _)).trans_eq (sum_modes m hAP)
  have hv := (truncation hV hAP Y hY).2
  rw [he] at hv
  linarith

theorem logarithmic_cutoff {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) (Y : ℕ) (hY : 0<Y) (hl : 8≤Real.log Y) :
    V ≤ ∑ u∈through Y,u.mass+576*(2+Real.log Y)^5/Y := by
  apply (truncation hV hAP Y hY).2.trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10) (show 10≤2+Real.log Y by linarith) 5
  linarith

#print axioms period_bound
#print axioms logarithmic_cutoff
#print axioms truncation
end
end Arxiv.«2501.03234».ThetaInverseConductorTail
