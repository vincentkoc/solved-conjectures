import ThetaWindowPrimeBand
import ThetaShortIntervalEnergy
import ThetaCalibratedCone

/-! Finite exceptional counts for the original signed theta sum. -/
namespace Arxiv.«2501.03234».ThetaShortPrimeBand
open Finset Real ThetaReciprocalInversion ThetaRowCorrelations ThetaSmoothConditionalModel
open ThetaDenominatorTails ThetaIdentityModels
noncomputable section

/-- Translated energy in the high rows at the cone cutoff. -/
theorem high_rows {e : ℕ} (h32 : 32≤e) (h48 : e≤48) :
    ∃ B : ℝ, 0<B ∧ ∀ {N T : ℕ}, 2≤N → 2≤T → ∀ (M H : ℕ) (L : ℕ → ℕ),
    (∑ i∈range H, ‖windowExtension (above T L) (2*ThetaCalibratedCone.cutoff e N) (M+i)‖^2) ≤
      B*(1+log N)^8*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(N:ℝ)^e) := by
  obtain ⟨B,hB,hv⟩ := ThetaShortIntervalEnergy.cut
  refine ⟨8*B,by positivity,?_⟩
  intro N T hN hT M H L
  let J := ThetaCalibratedCone.cutoff e N
  obtain ⟨hlo,hhi,hJcost⟩ := ThetaCalibratedCone.cutoff_bounds h32 h48 (show 1≤N by omega)
  have hj : 0<J := (pow_pos (by omega : 0<N) 2).trans_le hlo
  have hJcap : J≤N^52 := hhi.trans (Nat.pow_le_pow_right (by omega) (by decide))
  apply (hv (T:=T) (by omega) (above T L) (fun d hd => by simp [above,hd]) (by omega : 1≤N) hj hJcap M H).trans
  let V := 1+log (N:ℝ)
  let E := (H:ℝ)/(T:ℝ)^(1/64:ℝ)
  have hv1 : 1≤V := by dsimp [V];linarith only [log_nonneg (by exact_mod_cast (show 1≤N by omega) : 1≤(N:ℝ))]
  have he : 0≤E := by dsimp [E];positivity
  have hv3 : 1≤V^3 := one_le_pow₀ hv1
  have hE : E≤8*V^3*E := by nlinarith only [mul_le_mul_of_nonneg_right hv3 he,he]
  change (J:ℝ)≤8*(N:ℝ)^e*V^3 at hJcost
  have hsum : E+(J:ℝ)≤8*V^3*(E+(N:ℝ)^e) := by linarith only [hE,hJcost]
  exact (mul_le_mul_of_nonneg_left hsum (show 0≤B*V^5 by positivity [le_trans zero_le_one hv1])).trans_eq (by ring)


/-- Markov on a low-row moment and the high-row variance. The moment order and
denominator cutoff can both grow with the endpoint. -/
theorem prime_band {e : ℕ} (h32 : 32≤e) (h48 : e≤48) (kernel : ThetaCalibratedCone.Kernel e) : ∃ C a K B : ℝ, 0<C ∧ 0<a ∧ 0<K ∧ 0<B ∧
    ∀ {N T : ℕ}, 2≤N → 2≤T → T≤N^2 → ∀ (M H k : ℕ) {u : ℝ}, 0<u → ∀ s : Finset ℕ,
    (∀ i∈s,i<H ∧ (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
      C+(8/Real.pi^2)*(u+1)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) →
    (s.card:ℝ) ≤ B*(1+log N)^8*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(N:ℝ)^e) +
      (((H:ℝ)*K*((2*k:ℕ)/a)^(2*k) + 2*(6*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) := by
  obtain ⟨C,hC,ctrl⟩ := ThetaCalibratedCone.scale_window_control h32 h48 kernel
  obtain ⟨a,K,ha,hK,hm⟩ := ThetaWindowFiniteMoments.translated_moment
  obtain ⟨B,hB,hv⟩ := high_rows h32 h48
  refine ⟨C,a,K,B,hC,ha,hK,hB,?_⟩
  intro N T hN hT hTY M H k u hu s hs
  let J := ThetaCalibratedCone.cutoff e N
  let L := coneWindow (ThetaPrimeMeanSquare.coneWidth N)
  have hL : L 1=0 := by simp [L,coneWindow]
  obtain ⟨hlo,hhi,_⟩ := ThetaCalibratedCone.cutoff_bounds h32 h48 (show 1≤N by omega)
  have hJcap : J≤N^52 := hhi.trans (Nat.pow_le_pow_right (by omega) (by decide))
  apply ThetaWindowPrimeBand.from_moments hN (show T≤2*J by dsimp [J];omega)
    (Nat.mul_le_mul_left 2 hJcap) M H k hu L hL (fun _ => ctrl hN) _ (hm T ⟨L,2*J⟩ hT M H (2*k)) s hs
  exact hv hN hT M H L

#print axioms prime_band
end
end Arxiv.«2501.03234».ThetaShortPrimeBand
