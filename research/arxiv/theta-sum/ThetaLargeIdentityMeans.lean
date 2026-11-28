import ThetaLargeIdentityModels
import ThetaIdentityPrimeMeans

/-! The conditional prime mean on an explicit factorial progression grows quadratically in its logarithmic parameter. -/
namespace Arxiv.«2501.03234».ThetaLargeIdentityMeans
open Filter ThetaOddHarmonicTriangle ThetaFactorialSequence ThetaNaturalPrimeMeans ThetaDyadicLaw
open ThetaDiagonalConstant ThetaCharacterPrimeMeans
open scoped Topology

/-- Every sufficiently large member of the prescribed family has an ordinary
class mean for the original residual at least B + (log T)²/(16π²). -/
theorem means (hAP : ProgressionMangoldt) :
    ∀ᶠ T : ℕ in atTop, ∃ L : ℝ, diagonalConstant+(Real.log T)^2/(16*Real.pi^2) ≤ L ∧
      Tendsto (progressionMean (modulus T) 1 (fun p => (S p:ℝ)/p-Real.log p/2)) atTop (𝓝 L) := by
  have hlog : Tendsto (fun t : ℕ => Real.log (t:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ThetaLargeIdentityModels.growing_models,hlog.eventually_ge_atTop 16,eventually_ge_atTop (1:ℕ)] with T hm hl ht
  obtain ⟨L,hL,h⟩ := ThetaIdentityPrimeMeans.transfer hAP hm.1 hm.2
  refine ⟨L,?_,h⟩
  have hlo : Real.log T ≤ (harmonic T:ℝ) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ T)).trans (log_add_one_le_harmonic T)
  have hu := odd_harmonic_lower T
  have hl' : 16≤ Real.log T := hl
  have hpos : 8≤ H T := by linarith
  have hsq : (Real.log T)^2 ≤ (2*H T)^2 := pow_le_pow_left₀ (by linarith) (by linarith) _
  have hG : (Real.log T)^2/128 ≤ (H T^2/4-H T)/2-1/4 := by
    nlinarith only [hsq,hpos,mul_nonneg (sub_nonneg.mpr hpos) (show 0≤ H T by linarith only [hpos])]
  apply le_trans _ hL
  apply add_le_add_right
  calc _ = (8/Real.pi^2)*((Real.log T)^2/128) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hG (by positivity)
#print axioms means
end Arxiv.«2501.03234».ThetaLargeIdentityMeans
