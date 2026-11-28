import ThetaTailMomentScale

/-! Sharp growth of the limiting absolute moments of the original prime residual. -/
namespace Arxiv.«2501.03234».ThetaSharpPrimeMoments
open Real Filter Finset MeasureTheory ThetaNaturalPrimeMeans ThetaProfiniteUnits ThetaPrimeLaw
open ThetaDiagonalConstant ThetaCharacterPrimeMeans ThetaDoubleExponentialLaw ThetaTailMomentScale
open ThetaResidualMoments ThetaDyadicLaw
open scoped Topology
noncomputable section

def scale (a : ℝ) (k : ℕ) := (a*log k)^2

theorem grows {a : ℝ} (ha : 0<a) : Tendsto (scale a) atTop atTop :=
  (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp ((tendsto_const_mul_atTop_of_pos ha).mpr
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem scale_sqrt {a : ℝ} (ha : 0≤a) {k : ℕ} (hk : 1≤k) : sqrt (scale a k)=a*log k :=
  sqrt_sq (mul_nonneg ha (log_nonneg (by exact_mod_cast hk)))

def moment (μ : ProbabilityMeasure ℝ) (k : ℕ) :=
  ∫ x, |x-diagonalConstant|^k ∂(μ:Measure ℝ)

theorem order (hAP : ProgressionMangoldt) : ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ k : ℕ in atTop,
    ∀ F : G →₁[haar] ℝ, Represents residual F →
    (a*(log k)^2)^k≤ moment (haarLaw F) k ∧ moment (haarLaw F) k≤(C*(log k)^2)^k := by
  obtain ⟨c,hc,H⟩ := two_sided hAP
  obtain ⟨T,hT⟩ := eventually_atTop.mp H
  let l := 1/(32*π)
  let u := 2/c
  have hl : 0<l := by dsimp [l];positivity
  have hu : 0<u := by dsimp [u];positivity
  refine ⟨exp (-1)*l^2,2*u^2,by positivity,by positivity,?_⟩
  have hlog := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [(grows hl).eventually_ge_atTop T,(grows hu).eventually_ge_atTop T,
    eventually_ge_atTop 4,hlog] with k hk₁ hk₂ hk hlog
  intro F hF
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  change 1≤log (k:ℝ) at hlog
  have hlog' : 0<log k := by linarith
  have hroot : c*sqrt (scale u k)=2*log k := by
    rw [scale_sqrt hu.le (by omega)]
    dsimp [u];field_simp
  have hroot' : 32*π*sqrt (scale l k)=log k := by
    rw [scale_sqrt hl.le (by omega)]
    dsimp [l];field_simp
  have hsize : 4*(k:ℝ)≤exp (c*sqrt (scale u k)) := by
    rw [hroot,show (2:ℝ)*log k=log k+log k by ring,exp_add,exp_log hk']
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hk'.le
  have hi := upper_at (c:=c) (μ:=haarLaw F) (by unfold scale;positivity : 0<scale u k) (by rw [hroot];linarith)
    (by omega : 0<k) hsize (fun t ht => (hT t (hk₂.trans ht) F hF).2.2)
  have he := (hT _ hk₁ F hF).1
  rw [hroot',exp_log hk'] at he
  have hlo := lower_at (sq_nonneg (l*log k)) (exp_pos _).le hi.1 he
  constructor
  · apply le_trans (le_of_eq ?_) hlo
    rw [show -(k:ℝ)=(k:ℝ)*(-1) by ring,Real.exp_nat_mul,← mul_pow]
    congr 1;ring
  · apply hi.2.trans
    have hh : (2:ℝ)≤2^k := by
      calc (2:ℝ) = 2^1 := by norm_num
           _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ (2:ℝ)^k*(scale u k)^k := mul_le_mul_of_nonneg_right hh (by unfold scale;positivity)
      _ = _ := by rw [← mul_pow];congr 1;unfold scale;ring

theorem original (hAP : ProgressionMangoldt) : ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ᶠ k : ℕ in atTop,
    ∃ M : ℝ, (a*(log k)^2)^k≤M ∧ M≤(C*(log k)^2)^k ∧
      Tendsto (primeMean (fun p => |(S p:ℝ)/p-log p/2-diagonalConstant|^k)) atTop (𝓝 M) ∧
      ∀ l r : ℕ, r.Coprime (2^l) → r < 2^l →
        Tendsto (progressionMean (2^l) r (fun p => |(S p:ℝ)/p-log p/2-diagonalConstant|^k))
          atTop (𝓝 M) := by
  obtain ⟨a,C,ha,hC,H⟩ := order hAP
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  refine ⟨a,C,ha,hC,?_⟩
  filter_upwards [H] with k hk
  have hg (x : ℝ) : |(|x-diagonalConstant|^k)|≤(1+|diagonalConstant|)^k*(1+|x|^k) := by
    simpa only [abs_pow,abs_abs] using centered_growth diagonalConstant k x
  have hp : Continuous (fun x : ℝ => |x-diagonalConstant|^k) := by fun_prop
  exact ⟨_,(hk F hF).1,(hk F hF).2,(prime_polynomial_growth hAP hF hp hg).2,
    fun _ _ hr hh => dyadic_polynomial_growth hAP hF hr hh hp hg⟩

#print axioms order
#print axioms original
end
end Arxiv.«2501.03234».ThetaSharpPrimeMoments
