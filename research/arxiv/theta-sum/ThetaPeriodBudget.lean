import ThetaPrimePowerPacking
import ThetaInverseConductorTail
import ThetaProgressionProjection

/-! The least common multiple predictor gains a logarithm on the conductor cutoff. -/
namespace Arxiv.«2501.03234».ThetaPeriodBudget
open Finset Filter Topology ThetaNaturalPrimeMeans ThetaFiniteProjection ThetaLevelCoefficients
open ThetaSpectralVariance ThetaFullVarianceTail
noncomputable section

instance (Y : ℕ) : NeZero (Nat.lcmUpto Y) := ⟨Nat.lcmUpto_ne_zero Y⟩

/-- An admissible period of logarithmic size O(Y) misses only O(1/(Y log Y)) variance. -/
theorem lcm_prediction {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop,
      Real.log (Nat.lcmUpto Y)≤6*Y ∧ V-energy (Nat.lcmUpto Y)≤C/((Y:ℝ)*Real.log Y) := by
  classical
  obtain ⟨D,hD,H⟩ := ThetaPrimePowerPacking.omitted_conductors
  let A := 1152*(ThetaLValueMoment.H^3+1)
  have hA : 0<A := by
    have hH : 0≤ThetaLValueMoment.H := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
    dsimp [A]; positivity
  refine ⟨A*D,mul_pos hA hD,?_⟩
  filter_upwards [H] with Y hY
  constructor
  · rw [←Chebyshev.psi_eq_log_lcmUpto]
    have hh := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) Y)
    apply hh.trans
    have h4 : Real.log 4≤2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num only [Nat.cast_ofNat]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · let m := Nat.lcmUpto Y
    apply le_of_tendsto (ThetaFullVarianceTail.missing_mass hV hAP m)
    apply Eventually.of_forall
    intro s
    let t := s.filter (fun u : Mode => ¬u.modulus∣m)
    let c := t.image Mode.modulus
    have ht {u : Mode} (hu : u∈t) : ¬u.modulus∣m := (mem_filter.mp hu).2
    have hq {q : ℕ} (hq : q∈c) : 0<q ∧ ¬q∣m := by
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq; exact ⟨u.positive,ht hu⟩
    have he : ∑ u∈s,(if u.modulus∣m then 0 else u.mass)=∑ u∈t,u.mass := by
      dsimp [t]; rw [sum_filter]; simp only [ite_not]
    rw [he]
    calc
      _ = ∑ q∈c,∑ u∈t with u.modulus=q,u.mass :=
        (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem Mode.modulus hi) Mode.mass).symm
      _ ≤ ∑ q∈c,A*(1/((q:ℝ)*q.totient)) := by
        apply sum_le_sum; intro q hqc
        have hq₁ : 1<q := by
          have hh := hq hqc
          have hne : q≠1 := fun h => hh.2 (h ▸ one_dvd m)
          omega
        rw [mul_one_div]
        exact ThetaConductorMoment.level (t.filter (fun u => u.modulus=q))
          hq₁ (fun _ hu => (mem_filter.mp hu).2) hAP
      _ ≤ _ := by
        rw [←mul_sum]
        exact (mul_le_mul_of_nonneg_left (hY c (fun _ hu => hq hu)) hA.le).trans_eq (by ring)

end
end Arxiv.«2501.03234».ThetaPeriodBudget
#print axioms Arxiv.«2501.03234».ThetaPeriodBudget.lcm_prediction
