import ThetaLocalLipschitzTransfer

/-! The empirical probability law and every fixed signed moment on primes
in a moving short interval converge to the ordinary Haar residual law. -/
namespace Arxiv.«2501.03234».ThetaShortResidualLaw
open Real Filter Finset MeasureTheory ThetaLocalPrimeCounts ThetaLocalDyadicReference ThetaPrimeLaw
open ThetaLocalModelComparison ThetaPrimeDensity ThetaProfiniteUnits ThetaCharacterPrimeMeans
open ThetaLocalPrimeMomentLimits ThetaCalibratedCone ThetaNaturalPrimeMeans
open scoped Topology NNReal
noncomputable section

def actual (X H : ℕ) (f : ℕ → ℝ) := (∑ p∈sample X H,f p)/(sample X H).card

private def nonemptySample (X H : ℕ) : Finset ℕ := by
  classical
  exact if (sample X H).Nonempty then sample X H else {2}

private instance (X H : ℕ) : Nonempty ↥(nonemptySample X H) := by
  classical
  unfold nonemptySample
  split_ifs with h
  · exact h.to_subtype
  · exact ⟨⟨2,by simp⟩⟩

private def uniformSample (X H : ℕ) : ProbabilityMeasure ↥(nonemptySample X H) :=
  ⟨(PMF.uniformOfFintype _).toMeasure,inferInstance⟩

/-- The empirical probability law in the short interval, normalized by its prime count. -/
def law (X H : ℕ) (f : ℕ → ℝ) : ProbabilityMeasure ℝ :=
  (uniformSample X H).map (f:=fun p => f p.val) (measurable_of_countable _).aemeasurable

theorem integral_eq {X H : ℕ} (h : (sample X H).Nonempty)
    (f : ℕ → ℝ) {φ : ℝ → ℝ} (hp : Measurable φ) :
    (∫ x, φ x ∂(law X H f)) = actual X H (fun p => φ (f p)) := by
  rw [law,ProbabilityMeasure.toMeasure_map,integral_map (measurable_of_countable _).aemeasurable
    hp.aestronglyMeasurable]
  change (∫ p : ↥(nonemptySample X H), φ (f p.val) ∂(PMF.uniformOfFintype _).toMeasure) = _
  rw [PMF.integral_eq_sum]
  have hs : (∑ p : ↥(nonemptySample X H),φ (f p.val)) = ∑ p∈nonemptySample X H,φ (f p) :=
    Finset.sum_attach (nonemptySample X H) (fun p => φ (f p))
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,
    ← mul_sum,hs,Fintype.card_coe,actual,div_eq_inv_mul]
  rw [show nonemptySample X H = sample X H from if_pos h]


theorem normalize {θ : ℝ} (h : Ordinary θ) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop, H X≤X ∧ (X:ℝ)^θ≤H X) {f : ℕ → ℝ} {a : ℝ}
    (ha : Tendsto (fun X => avg X (H X) f) atTop (𝓝 a)) :
    Tendsto (fun X => actual X (H X) f) atTop (𝓝 a) := by
  have hcount : Tendsto (fun X => ((sample X (H X)).card:ℝ)/mass X (H X)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr;intro ε hε
    filter_upwards [relative_count h (half_pos hε),ThetaLocalMomentBudgets.count h,hh] with X hc hm hX
    rw [Real.dist_eq]
    have H := hc _ hX.1 hX.2
    have hnorm := normalized (u:=1) (hm _ hX.1 hX.2).1 (by simpa only [mul_one] using H)
    exact hnorm.trans_lt (half_lt_self hε)
  have result := ha.div hcount (by norm_num : (1:ℝ)≠0)
  rw [div_one] at result
  apply result.congr'
  filter_upwards [hh,ThetaLocalMomentBudgets.count h] with X hx hc
  have hm := (hc _ hx.1 hx.2).1
  dsimp [avg,actual];rw [div_div_div_cancel_right₀ hm.ne']

theorem populated {θ : ℝ} (h : Ordinary θ) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop, H X≤X ∧ (X:ℝ)^θ≤H X) : ∀ᶠ X : ℕ in atTop, (sample X (H X)).Nonempty := by
  filter_upwards [relative_count h (by norm_num : (0:ℝ)<1/2),ThetaLocalMomentBudgets.count h,hh] with X hC hm hx
  have h := (abs_le.mp (hC _ hx.1 hx.2)).1
  have hp := (hm _ hx.1 hx.2).1
  apply card_pos.mp
  exact_mod_cast (show (0:ℝ)<(sample X (H X)).card by linarith only [hp,h])

theorem lipschitz {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop, H X≤X ∧ (X:ℝ)^θ≤H X) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    Tendsto (fun X => actual X (H X) (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ (F x) ∂haar)) := by
  apply normalize h hh
  have hbase := dyadic hθ₁ h (prime_mean_lipschitz hAP hF hφ)
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have hdiff := ThetaLocalLipschitzTransfer.compare he h48 hk hθ hθ₁ h (q:=1) (by decide)
    (w:=fun _ => (1:ℝ)) (fun _ => rfl) (fun _ => by norm_num) hφ (half_pos hε)
  filter_upwards [hh,hdiff,Metric.tendsto_nhds.mp hbase _ (half_pos hε)] with X hx hc hb
  have hh := hc (H X) hx.1 hx.2
  simp only [one_mul] at hh
  rw [Real.dist_eq] at hb ⊢
  let f (p : ℕ) := φ (residual p)
  change |avg X X f-_|<_ at hb
  change |avg X (H X) f-avg X X f|<_ at hh
  exact (abs_sub_le _ (avg X X f) _).trans_lt (by linarith only [hh,hb])

/-- Every eligible sequence of short intervals has the same probability limit
as all primes through X. -/
theorem weak {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop, H X≤X ∧ (X:ℝ)^θ≤H X) :
    Tendsto (fun X => law X (H X) residual) atTop (𝓝 (haarLaw F)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ _ ⟨K,hK⟩
  rw [haarLaw_integral F hK.continuous]
  exact (lipschitz he h48 hk hθ hθ₁ h hAP hF hh hK).congr' ((populated h hh).mono fun X hx =>
    (integral_eq hx residual hK.continuous.measurable).symm)

theorem moments {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop, H X≤X ∧ (X:ℝ)^θ≤H X) (k : ℕ) :
    Tendsto (fun X => actual X (H X) (fun p => (residual p)^k)) atTop
      (𝓝 (∫ x, x^k ∂(haarLaw F : Measure ℝ))) := by
  have hglobal := (ThetaResidualMoments.prime_polynomial_growth hAP hF (φ:=fun x : ℝ => x^k) (continuous_pow k)
    (K:=1) (k:=k) (fun x => by rw [←pow_abs];linarith only [pow_nonneg (abs_nonneg x) k])).2
  apply normalize h hh
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have ht := transfer he h48 hk hθ hθ₁ h (q:=1) (by decide) (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
    (fun _ => rfl) (fun _ => rfl) (fun _ => by norm_num) (D:=0) (fun _ => by norm_num) k (a:=∫ x, x^k ∂(haarLaw F : Measure ℝ))
    (by simpa only [one_mul,zero_add] using hglobal) hε
  simp only [one_mul,zero_add] at ht
  filter_upwards [ht,hh] with X ht hx
  exact ht _ hx.1 hx.2

#print axioms weak
#print axioms moments
end
end Arxiv.«2501.03234».ThetaShortResidualLaw
