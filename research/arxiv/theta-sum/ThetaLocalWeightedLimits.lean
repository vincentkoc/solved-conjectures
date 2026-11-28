import ThetaShortResidualLaw

/-! Every fixed periodic weight and Lipschitz residual test has a common
long and short prime mean. -/
namespace Arxiv.«2501.03234».ThetaLocalWeightedLimits
open Real Filter Finset MeasureTheory ThetaPrimeLaw ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open ThetaLocalPrimeCounts ThetaLocalDyadicReference ThetaPrimeDensity ThetaCalibratedCone ThetaPeriodMeans
open scoped Topology NNReal
noncomputable section

theorem approximable {q : ℕ} (hq : 0<q) {w : ℕ → ℝ} (hw : OnMod q w)
    (hB : ∀ n, |w n|≤1) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    Approximable (fun p => w p*φ (residual p)) := by
  intro ε hε
  let t := ε/((K:ℝ)+1)
  have ht : 0<t := by dsimp [t]; positivity
  obtain ⟨T,V,hg⟩ := residual_model_approximation ht
  let J := max q T
  have hp : q∣J.factorial := Nat.dvd_factorial hq (le_max_left ..)
  have hT : T.factorial∣J.factorial := Nat.factorial_dvd_factorial (le_max_right ..)
  let b := residualModel T V
  refine ⟨J,fun p => w p*φ (b p),fun n => congrArg₂ (·*·) (onMod_lift hp hw n)
    (congrArg φ (onMod_lift hT (residualModel_periodic T V) n)),?_⟩
  filter_upwards [hg] with X hx
  have h (p : ℕ) : |w p*φ (residual p)-w p*φ (b p)|≤K*|residual p-b p| := by
    rw [←mul_sub,abs_mul];exact (mul_le_of_le_one_left (abs_nonneg _) (hB p)).trans (hφ.dist_le_mul ..)
  have hh := div_le_div_of_nonneg_right (sum_le_sum (s:=Nat.primesLE X) (fun p _ => h p))
    (Nat.cast_nonneg X.primeCounting (α:=ℝ))
  rw [←mul_sum,mul_div_assoc] at hh
  apply hh.trans
  change (K:ℝ)*_≤_
  apply (mul_le_mul_of_nonneg_left hx K.2).trans
  have heq : ((K:ℝ)+1)*t=ε := by dsimp [t];field_simp
  exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1) : (K:ℝ)≤(K:ℝ)+1) ht.le).trans_eq heq

theorem common {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q : ℕ} (hq : 0<q) {w : ℕ → ℝ} (hw : OnMod q w) (hB : ∀ n, |w n|≤1)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∃ a : ℝ, let f (p : ℕ) := w p*φ (residual p)
    Tendsto (primeMean f) atTop (𝓝 a) ∧ ∀ ε : ℝ, 0<ε → ∀ᶠ X : ℕ in atTop,
      ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H → |avg X H f-a|<ε := by
  let f (p : ℕ) := w p*φ (residual p)
  obtain ⟨F,hF⟩ := exists_haar_representative hAP (approximable hq hw hB hφ)
  have hl := prime_mean_lipschitz hAP hF LipschitzWith.id
  let a := ∫ x, F x ∂ThetaProfiniteUnits.haar
  change Tendsto (primeMean f) atTop (𝓝 a) at hl
  refine ⟨a,hl,?_⟩
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp (ThetaLocalPrimeMomentLimits.dyadic hθ₁ h hl) (ε/2) (half_pos hε),
      ThetaLocalLipschitzTransfer.compare he h48 hk hθ hθ₁ h hq hw hB hφ (half_pos hε)] with X hd hs
  intro H hHX hlen
  rw [Real.dist_eq] at hd
  have H : |avg X H f-avg X X f|<ε/2 := hs H hHX hlen
  exact (abs_sub_le _ (avg X X f) _).trans_lt (by linarith only [hd,H])

#print axioms common
end
end Arxiv.«2501.03234».ThetaLocalWeightedLimits
