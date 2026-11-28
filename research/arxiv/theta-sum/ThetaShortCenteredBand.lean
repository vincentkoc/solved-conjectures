import ThetaShortPrimeBand
import ThetaCenteredMoment

/-! Translated finite moments after removing the small-prime average. -/
namespace Arxiv.«2501.03234».ThetaShortCenteredBand
open Finset Filter Real ThetaReciprocalInversion ThetaRowCorrelations ThetaSmoothConditionalModel
open ThetaShortPrimeBand ThetaCenteredMoment ThetaCenteredWindow ThetaIdentityModels ThetaTiltBudget
noncomputable section

theorem prime_band {e : ℕ} (h32 : 32≤e) (h48 : e≤48) (kernel : ThetaCalibratedCone.Kernel e) :
    ∃ C B : ℝ, 0<C ∧ 0<B ∧ ∀ᶠ U : ℕ in atTop,
    ∀ {N T : ℕ}, 2≤N → 2≤T → T≤N^2 → ∀ (M H k : ℕ) {u : ℝ}, 0<u → ∀ s : Finset ℕ,
    (∀ i∈s,i<H ∧ (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
      C+(8/Real.pi^2)*(u+ThetaModelExponentialMoment.height U+1)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) →
    (s.card:ℝ) ≤ B*(1+log N)^8*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(N:ℝ)^e) +
       (((H:ℝ)*(2*exp total)*((2*k:ℕ)/tilt U)^(2*k)+2*(12*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) := by
  obtain ⟨C,hC,ctrl⟩ := ThetaCalibratedCone.scale_window_control h32 h48 kernel
  obtain ⟨B,hB,hv⟩ := high_rows h32 h48
  refine ⟨C,B,hC,hB,?_⟩
  have hlog := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [translated,hlog,eventually_ge_atTop 2] with U hm hl hU
  intro N T hN hT hTY M H k u hu s hs
  let J := ThetaCalibratedCone.cutoff e N
  let L := coneWindow (ThetaPrimeMeanSquare.coneWidth N)
  let W : Window := ⟨L,2*J⟩
  have hL : L 1=0 := by simp [L,coneWindow]
  obtain ⟨hlo,hhi,_⟩ := ThetaCalibratedCone.cutoff_bounds h32 h48 (show 1≤N by omega)
  have hJcap : J≤N^52 := hhi.trans (Nat.pow_le_pow_right (by omega) (by decide))
  apply ThetaWindowPrimeBand.from_approximation hN (show T≤2*J by dsimp [J];omega)
    (Nat.mul_le_mul_left 2 hJcap) M H k hu L hL (fun _ => ctrl hN) (hv hN hT M H L)
    (fun i => center T U W (M+i)) _ (hm T W M H (2*k)) s hs
  intro i _
  have hb := ThetaOrbitProjection.smooth_baseline hT hU hl W (M+i)
  have hh := abs_add_le (center T U W (M+i)) (ThetaOrbitProjection.smooth T U (rowModel T W) (M+i))
  simp only [center,sub_add_cancel] at hh
  exact hh.trans (add_le_add_right hb _)

#print axioms prime_band
end
end Arxiv.«2501.03234».ThetaShortCenteredBand
