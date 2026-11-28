import ThetaPrimeAnchorTransfer
import ThetaAlmostWindowLaw
import ThetaPrimeQuantiles

/-! Uniform prime-start approximation for the signed residual and continuous
tests of polynomial growth. -/
namespace Arxiv.«2501.03234».ThetaPrimeAnchorTests
open Real Filter Finset MeasureTheory ThetaWindowApproximation ThetaAlmostPeriodicWindows
open ThetaPrimeStartDensity ThetaPrimeAnchorTransfer ThetaLocalPrimeCounts ThetaNaturalPrimeMeans
open ThetaCharacterPrimeMeans ThetaProfiniteUnits ThetaPrimeLaw ThetaLocalIntervalTests
open scoped Topology
noncomputable section

theorem growth {φ : ℝ → ℝ} {K : ℝ} (hK : 0≤K) (k : ℕ) (hg : ∀ x, |φ x|≤K*(1+|x|^k)) :
    Controlled (fun p => φ (residual p)) := by
  obtain ⟨M,hM,hm⟩ := ThetaPrimeQuantiles.pointwise
  refine ⟨(K+1)*(1+(4*M)^k),by positivity,2*k,?_⟩
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hl.eventually_ge_atTop (max 1 (log 3)),eventually_ge_atTop (1:ℕ)] with X hL hx
  intro p hp _ hbig
  have hl₁ : 1≤log (X:ℝ) := (le_max_left ..).trans hL
  have hl₂ : log 3≤log (X:ℝ) := (le_max_right ..).trans hL
  have hx' : 0<(X:ℝ) := by exact_mod_cast hx
  have hlog : log ((3*X:ℕ):ℝ)=log 3+log X := by push_cast;rw [log_mul (by norm_num) hx'.ne']
  have h₃ : 0≤log 3 := log_nonneg (by norm_num)
  have hb := hm (3*X) p (by rw [hlog];linarith) hp hbig
  rw [hlog] at hb
  have hpow := pow_le_pow_left₀ (by linarith : 0≤log 3+log (X:ℝ)) (by linarith : log 3+log X≤2*log X) 2
  have hr : |residual p|≤4*M*(log X)^2 := hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hpow hM.le])
  have hs := pow_le_pow_left₀ (abs_nonneg (residual p)) hr k
  rw [mul_pow,← pow_mul] at hs
  have hone : 1≤(log (X:ℝ))^(2*k) := one_le_pow₀ hl₁
  have hc := (hg (residual p)).trans (mul_le_mul_of_nonneg_left (add_le_add_right hs 1) hK)
  have h₁ := mul_le_mul_of_nonneg_left hone hK
  have h₂ := mul_nonneg (pow_nonneg (by positivity : 0≤4*M) k) (le_trans zero_le_one hone)
  exact hc.trans (by nlinarith only [h₁,h₂,hone])

theorem limit {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {f : ℕ → ℝ} (hc : Controlled f) (hf : Approximable f) {a : ℝ} (ha : Tendsto (primeMean f) atTop (𝓝 a))
    {ε : ℝ} (he : 0<ε) : Typical (fun X n => ∀ H : ℕ,Admits θ X H → |avg X n H f-a|≤ε) := by
  apply ThetaPrimeAnchorTransfer.transfer (P:=fun b => |b-a|≤ε/2) (Q:=fun b => |b-a|≤ε)
    ht ht' hc (half_pos he) _ (ThetaAlmostTransfer.limit h hAP hf ha (half_pos he))
  intro x y h₁ h₂
  exact (abs_sub_le x y a).trans (by linarith only [h₁,h₂])

theorem polynomial {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {K : ℝ} (hK : 0≤K) (k : ℕ) (hg : ∀ x, |φ x|≤K*(1+|x|^k)) {ε : ℝ} (he : 0<ε) :
    Typical (fun X n => ∀ H : ℕ,Admits θ X H → |avg X n H (fun p => φ (residual p))-
      (∫ x, φ x ∂(haarLaw F : Measure ℝ))|≤ε) :=
  limit ht ht' h hAP (growth hK k hg) (ThetaPrimeTestApproximation.original hAP hF hφ hK k hg)
    (ThetaResidualMoments.prime_polynomial_growth hAP hF hφ hg).2 he

#print axioms polynomial
end
end Arxiv.«2501.03234».ThetaPrimeAnchorTests
