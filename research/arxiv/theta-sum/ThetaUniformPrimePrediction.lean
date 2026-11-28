import ThetaClassConcentration
import ThetaConditionalApproximation

/-! The arithmetic progression predictor approximates the original signed
residual in class-normalized mean absolute error, uniformly over reduced
classes of each compact modulus. -/
namespace Arxiv.«2501.03234».ThetaUniformPrimePrediction
open Finset Real Filter ThetaClassConcentration ThetaConditionalApproximation ThetaDyadicLaw
open ThetaPrimeLaw ThetaPrimeTailTransfer ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open ThetaProgressionProjection ThetaSmoothConditionalModel ThetaIdentityFiber ThetaConditionalRows
open ThetaDiagonalConstant ThetaPeriodMeans ThetaTiltBudget ThetaPrimeDensity
open scoped Topology
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
local instance (T : ℕ) : NeZero (m T) := ⟨(ThetaCompactModulus.positive T).ne'⟩

def rate (T : ℕ) := (16/π^2)*(bias T+2*exp total/tilt T)
def prediction (T r : ℕ) := diagonalConstant+predictor (m T) r

theorem rate_zero : Tendsto rate atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℕ => (log (T:ℝ))^2/(T:ℝ)^(1/16:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/16)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hb := hl.const_mul ((2160*ThetaIdentityModels.Z)*(612*ThetaFactorialRows.zetaBound))
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h := (hb.add (ht.const_div_atTop (2*exp total))).const_mul (16/π^2)
  simp only [mul_zero,add_zero] at h
  apply h.congr
  intro T
  dsimp [rate,bias,tilt]; ring

theorem original (hAP : ProgressionMangoldt) :
    ∀ᶠ T : ℕ in atTop, ∀ ε : ℝ, 0<ε → ∀ᶠ X : ℕ in atTop, ∀ r< m T, r.Coprime (m T) →
      progressionMean (m T) r (fun p => |(S p:ℝ)/p-log p/2-prediction T r|) X≤rate T+ε := by
  filter_upwards [ThetaClassConcentration.finite] with T hmod
  intro ε he
  let M := m T
  have hm : 0<M := ThetaCompactModulus.positive T
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  let c := 8/π^2
  have hc : 0<c := by dsimp [c]; positivity
  let δ := ε/(32*(M.totient:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨Y,hY,hY'⟩ := ((eventually_ge_atTop M).and (residual_models_approximate hδ)).exists
  obtain ⟨V,hV⟩ := hY'.exists
  have hd := Nat.dvd_factorial hm hY
  let g := residualModel Y V
  let B := bias T+2*exp total/tilt T
  have each (r : ℕ) (hr : r < M) (hu : r.Coprime M) : ∀ᶠ X : ℕ in atTop,
      progressionMean M r (fun p => |(S p:ℝ)/p-log p/2-prediction T r|) X≤rate T+ε := by
    let a := diagonalConstant+c*cond M r Y (standardWindow V)
    let u (n : ℕ) := |g n-a|
    let v (n : ℕ) := selectClass r M n*|rowModel Y (standardWindow V) n-cond M r Y (standardWindow V)|
    have hper : OnMod Y.factorial u := fun n => by dsimp only [u,g];rw [residualModel_periodic Y V n]
    have mean := periodic hAP hm hd hr hu hper
    have finite := hmod Y hd (standardWindow V) r hr hu
    change (M.totient:ℝ)*unitMean Y.factorial v≤B at finite
    have eqn (n : ℕ) : selectClass r M n*u n=c*(v n) := by
      have h : g n-a=c*(rowModel Y (standardWindow V) n-cond M r Y (standardWindow V)) := by
        dsimp only [g,a,residualModel,c]; change _=8/π^2*(model Y V n-_); ring
      rw [show u n=|g n-a| from rfl,h,abs_mul,abs_of_pos hc]; dsimp only [v]; ring
    have hlim : (M.totient:ℝ)*unitMean Y.factorial (fun n => selectClass r M n*u n)≤c*B := by
      apply le_trans _ (mul_le_mul_of_nonneg_left finite hc.le)
      rw [show (fun n => selectClass r M n*u n)=(fun n => c*v n) from funext eqn]
      unfold unitMean; rw [←mul_sum]; exact le_of_eq (by ring)
    have hgp := mean.eventually_le_const (by linarith only [hlim,he] :
      (M.totient:ℝ)*unitMean Y.factorial (fun n => selectClass r M n*u n)<c*B+ε/8)
    have herr := restrict_error hAP hm hr hu (fun n => abs_nonneg (residual n-g n)) hV
    have hμ := Metric.tendsto_nhds.mp (original_mean M r hu hr hAP) (ε/8) (by positivity)
    filter_upwards [hgp,herr,hμ,class_nonempty hAP hm hu hr] with X hg hv hμ hne
    have H := recenter hne residual g a (prediction T r)
    change progressionMean M r _ X≤2*(progressionMean M r (fun p => |residual p-g p|) X+progressionMean M r u X)+
      |progressionMean M r residual X-prediction T r| at H
    have heq : 2*(M.totient:ℝ)*δ=ε/16 := by dsimp only [δ]; field_simp;ring
    rw [heq] at hv
    rw [Real.dist_eq] at hμ
    change |progressionMean M r residual X-prediction T r|<ε/8 at hμ
    change progressionMean M r (fun p => |residual p-prediction T r|) X≤(16/π^2)*B+ε
    rw [show (16/π^2)*B=2*((8/π^2)*B) by ring]
    change progressionMean M r u X≤(8/π^2)*B+ε/8 at hg
    linarith only [H,hv,hg,hμ,he]
  have H : ∀ᶠ X : ℕ in atTop, ∀ r∈range M, r.Coprime M →
      progressionMean M r (fun p => |residual p-prediction T r|) X≤rate T+ε := (eventually_all_finset (range M)).mpr (fun r hr => by
    by_cases hc : r.Coprime M
    · filter_upwards [each r (mem_range.mp hr) hc] with X hX using (fun _ => hX)
    · exact Eventually.of_forall (fun _ h => (hc h).elim))
  filter_upwards [H] with X hX
  exact fun r hr hc => hX r (mem_range.mpr hr) hc

#print axioms rate_zero
#print axioms original
end
end Arxiv.«2501.03234».ThetaUniformPrimePrediction
