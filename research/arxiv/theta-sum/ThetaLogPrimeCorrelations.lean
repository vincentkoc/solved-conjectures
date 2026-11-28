import ThetaProgressionTailPairs
import ThetaPrimeQuantiles

/-! Raw residual correlation and signed energy of four distinct primes
survive subtraction of every predictor of a prescribed period. -/
namespace Arxiv.«2501.03234».ThetaLogPrimeCorrelations
open Real Filter Finset ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPeriodMeans
open ThetaPeriodicCorrelationWitness ThetaLogarithmicLags ThetaPositiveLag ThetaPrimeLagBounds
open ThetaDistinctPrimeQuadruples
open scoped Topology
noncomputable section

theorem controlled {m : ℕ} [NeZero m] {g : ℕ → ℝ} (hg : OnMod m g) :
    Controlled (fun p => residual p-g p) := by
  obtain ⟨M,hM,H⟩ := ThetaPrimeQuantiles.pointwise
  obtain ⟨B,hB,hb⟩ := periodic_bound hg
  refine ⟨M+B,by positivity,2,?_⟩
  filter_upwards [(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1] with X hX
  change 1≤log X at hX
  intro p hp
  obtain ⟨h₁,h₂⟩ := Nat.mem_primesLE.mp hp
  have hR : |residual p|≤M*(log X)^2 := H X p hX h₂ h₁
  nlinarith only [abs_sub (residual p) (g p),hR,hb p,
    mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) hX) hB]

theorem original (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ q : ℕ,m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ c : ℝ,0<c ∧ ∀ g : ℕ → ℝ,OnMod m g →
      (∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop,∃ h : ℕ,0<h ∧ q∣h ∧ (h:ℝ)≤A*log X ∧
        c*X≤corr X h (fun p => (S p:ℝ)/p-log p/2-g p)*(log X)^2) ∧
      ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,∀ L : ℕ,K*log X≤L → q*L≤X →
        c^2/2*(X:ℝ)^2*L≤(∑ k∈offsets L,four X (q*k) (fun p => (S p:ℝ)/p-log p/2-g p))*(log X)^4 := by
  obtain ⟨q,hq,hqr,h₃,c,hc,H⟩ := scales (m:=m) hAP
  exact ⟨q,hq,hqr,h₃,c,hc,fun g hg => ⟨short hqr.pos hc (H g hg),
    ThetaDistinctPrimeQuadruples.energy hqr.pos hc (H g hg) (controlled hg)⟩⟩

#print axioms original
end
end Arxiv.«2501.03234».ThetaLogPrimeCorrelations
