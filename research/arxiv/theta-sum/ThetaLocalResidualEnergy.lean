import ThetaLocalCenteredApproximation
import ThetaLocalExcursionScales

/-! Translated square energy for the enlarged cutoff and the original prime residual. -/
namespace Arxiv.«2501.03234».ThetaLocalResidualEnergy
open Real Finset Filter ThetaLocalVanishingCone ThetaDenominatorTails ThetaReciprocalInversion
open ThetaLocalCenteredApproximation ThetaCharacterPrimeMeans ThetaPrimeLaw ThetaLocalPrimeCounts
open ThetaShortPrimeInterval ThetaPrimeMeanSquare ThetaLocalExcursionScales ThetaCalibratedCone
noncomputable section

theorem high_rows {e : ℕ} (h32 : 32≤e) (h48 : e≤48) :
    ∃ B : ℝ, 0<B ∧ ∀ {N T : ℕ}, 2≤N → 2≤T → ∀ (M H : ℕ) (L : ℕ → ℕ),
    (∑ i∈range H, ‖windowExtension (above T L) (2*fine e N) (M+i)‖^2) ≤
      B*(1+log N)^9*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(N:ℝ)^e) := by
  obtain ⟨B,hB,hv⟩ := ThetaShortIntervalEnergy.cut
  refine ⟨16*B,by positivity,?_⟩
  intro N T hN hT M H L
  let J := fine e N
  obtain ⟨hlo,hhi,hJcost⟩ := bounds h32 h48 (show 1≤N by omega)
  have hj : 0<J := (pow_pos (by omega : 0<N) 2).trans_le hlo
  have hJcap : J≤N^52 := hhi
  apply (hv (T:=T) (by omega) (above T L) (fun d hd => by simp [above,hd]) (by omega : 1≤N) hj hJcap M H).trans
  let V := 1+log (N:ℝ)
  let E := (H:ℝ)/(T:ℝ)^(1/64:ℝ)
  have hv1 : 1≤V := by dsimp [V];linarith only [log_nonneg (by exact_mod_cast (show 1≤N by omega) : 1≤(N:ℝ))]
  have he : 0≤E := by dsimp [E];positivity
  have hv3 : 1≤V^4 := one_le_pow₀ hv1
  have hE : E≤16*V^4*E := by nlinarith only [mul_le_mul_of_nonneg_right hv3 he,he]
  change (J:ℝ)≤16*(N:ℝ)^e*V^4 at hJcost
  have hsum : E+(J:ℝ)≤16*V^4*(E+(N:ℝ)^e) := by linarith only [hE,hJcost]
  exact (mul_le_mul_of_nonneg_left hsum (show 0≤B*V^5 by positivity [le_trans zero_le_one hv1])).trans_eq (by ring)



theorem sample_energy (F : ℕ → ℂ) (X H : ℕ) :
    (∑ p∈sample X H,‖F p‖^2)≤∑ i∈range H,‖F (X+1+i)‖^2 := by
  have hsub : sample X H⊆(range H).image ((X+1)+·) := by
    intro p hp
    obtain ⟨hi,_,_⟩ := mem_primes.mp hp
    obtain ⟨hx,hy⟩ := mem_Ioc.mp hi
    exact mem_image.mpr ⟨p-(X+1),mem_range.mpr (by omega),by omega⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg ‖F p‖)).trans_eq
  rw [sum_image (fun _ _ _ _ hv => Nat.add_left_cancel hv)]

theorem interval {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {η : ℝ} (hη : 0<η) :
    ∃ B : ℝ, 0<B ∧ ∀ᶠ N : ℕ in atTop, ∀ {T X H : ℕ}, 2≤T → T≤N →
    N^56≤X → X+H≤N^64 →
    (∑ p∈sample X H,(residual p-residualModel T N p)^2)≤
      3*(η^2+((8/π^2)*(3*(T:ℝ)/N))^2)*(sample X H).card+
      B*(1+log N)^9*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(N:ℝ)^e) := by
  obtain ⟨B,hB,hv⟩ := high_rows he h48
  let c := 8/π^2
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨3*c^2*B,by positivity,?_⟩
  filter_upwards [signed he h48 hk hη,eventually_ge_atTop (2:ℕ)] with N ha hN
  intro T X H hT hTN hl hh
  let K := coneWindow (coneWidth N)
  let F := windowExtension (above T K) (2*fine e N)
  let d := c*(3*(T:ℝ)/N)
  have hsq (p : ℕ) (hp : p∈sample X H) :
      (residual p-residualModel T N p)^2≤3*(η^2+d^2)+3*c^2*‖F p‖^2 := by
    obtain ⟨hp',hpr,_⟩ := mem_primes.mp hp
    obtain ⟨hx,hy⟩ := mem_Ioc.mp hp'
    have h := ha hTN hpr (hl.trans hx.le) (hy.trans hh)
    change |residual p-residualModel T N p|≤η+c*(3*(T:ℝ)/N+‖F p‖) at h
    have hp := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hp
    have heq : η+c*(3*(T:ℝ)/N+‖F p‖)=η+d+c*‖F p‖ := by dsimp [d];ring
    rw [heq] at hp
    nlinarith only [hp,sq_nonneg (η-d),sq_nonneg (d-c*‖F p‖),sq_nonneg (c*‖F p‖-η)]
  have hsum := (sample_energy F X H).trans (hv hN hT (X+1) H K)
  apply (sum_le_sum hsq).trans
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
  have HH := mul_le_mul_of_nonneg_left hsum (show 0≤3*c^2 by positivity)
  change _≤3*(η^2+d^2)*_+_
  linarith only [HH]

#print axioms high_rows
#print axioms interval
end
end Arxiv.«2501.03234».ThetaLocalResidualEnergy
