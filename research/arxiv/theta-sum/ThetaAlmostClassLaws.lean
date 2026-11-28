import ThetaAlmostPrimeDistribution
import ThetaClassResidualLaws

/-! Almost every starting integer and every admissible length have the
conditional Haar law and polynomial-growth tests in each reduced progression. -/
namespace Arxiv.«2501.03234».ThetaAlmostClassLaws
open Filter Finset Real MeasureTheory ThetaAlmostWindowLaw ThetaAlmostPeriodicWindows
open ThetaAlmostPrimeDistribution ThetaWindowApproximation ThetaPrimeLaw ThetaNaturalPrimeMeans
open ThetaProfiniteUnits ThetaConditionalHaar ThetaShortConditionalLaw ThetaShortClassMeans
open ThetaCharacterPrimeMeans ThetaIdentityFiber ThetaLocalPrimeCounts
open scoped Topology
noncomputable section

theorem denominator {θ : ℝ} (h : Equidistributed θ) {q r : ℕ} (hq : 0<q) (hr : r<q)
    (hu : r.Coprime q) :
    Tendsto (fun w : Window => scaledCount w.base w.start w.len q r) (windows θ) (𝓝 (1/(q.totient:ℝ))) := by
  apply Metric.tendsto_nhds.mpr;intro ε hε
  change Almost (fun X n => ∀ H : ℕ,Admits θ X H → dist (scaledCount X n H q r) _<ε)
  apply mono (h q hq (ε/2) (half_pos hε))
  filter_upwards with X
  intro n _ h₁ H hH
  have hc := h₁ H hH r hr
  rw [if_pos hu] at hc
  exact hc.trans_lt (half_lt_self hε)

theorem test {θ : ℝ} (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {φ : ℝ → ℝ} (hp : Continuous φ) {K : ℝ} (hK : 0≤K) (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k)) :
    Tendsto (fun w : Window => mean (window q r w.start w.len) (fun p => φ (residual p))) (windows θ)
      (𝓝 (∫ x,φ x ∂(law F (positive hAP hq hr hu)))) := by
  let f (p : ℕ) := φ (residual p)
  have ha := ThetaPrimeTestApproximation.original hAP hF hp hK k hg
  obtain ⟨Y,hY⟩ := exists_haar_representative hAP ha
  obtain ⟨Z,hZ,_⟩ := masked hY hq r
  have ha' : Approximable (fun p => selectClass r q p*f p) := by
    intro ε he
    obtain ⟨T,b,hb,hh,_⟩ := hZ ε he
    exact ⟨T,b,hb,hh⟩
  have hg' := ThetaClassResidualLaws.ordinary_tests hAP hq hr hu hF hp k hg
  have H := scaled h hAP ha' (factor hq hr hu hAP hg')
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hd := denominator h hq hr hu
  have hl := H.div hd (by positivity)
  rw [mul_comm (1/(q.totient:ℝ)),mul_div_cancel_right₀ _ (by positivity)] at hl
  apply hl.congr'
  filter_upwards [hd.eventually_const_lt (by positivity : 0<1/(q.totient:ℝ))] with w hx
  let c := log w.base/w.len
  change 0<c*((window q r w.start w.len).card:ℝ) at hx
  have hc : c≠0 := fun hh => by rw [hh,zero_mul] at hx;exact hx.false
  change (c*∑ p∈sample w.start w.len,selectClass r q p*f p)/(c*(window q r w.start w.len).card)=_
  rw [weighted_sum,mul_div_mul_left _ _ hc];rfl

theorem weak {θ : ℝ} (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    Tendsto (fun w : Window => ThetaWindowClassMeasure.law (window q r w.start w.len)) (windows θ)
      (𝓝 (law F (positive hAP hq hr hu))) := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hd := (denominator h hq hr hu).eventually_const_lt (by positivity : 0<1/(q.totient:ℝ))
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro ψ
  have hg (x : ℝ) : |ψ x|≤‖ψ‖*(1+|x|^0) := by
    have hh := ψ.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at hh
    simp only [pow_zero,one_add_one_eq_two];linarith only [hh,norm_nonneg ψ]
  apply (test h hAP hq hr hu hF ψ.continuous (norm_nonneg ψ) 0 hg).congr'
  filter_upwards [hd] with w hx
  change 0<log w.base/w.len*((window q r w.start w.len).card:ℝ) at hx
  have hn : (window q r w.start w.len).Nonempty := by
    by_contra he;rw [not_nonempty_iff_eq_empty.mp he] at hx;simp at hx
  exact (ThetaWindowClassMeasure.integral_eq hn ψ.continuous.measurable).symm

def ClassLaw (θ : ℝ) : Prop :=
    (windows θ).NeBot ∧ ∃ F : G →₁[haar] ℝ,Represents residual F ∧ ∀ q r : ℕ,0<q → r<q → r.Coprime q →
      ∃ hc : haar (fibre q r)≠0,
        Tendsto (fun w : Window => ThetaWindowClassMeasure.law (window q r w.start w.len)) (windows θ) (𝓝 (law F hc)) ∧
        ∀ φ : ℝ → ℝ,Continuous φ → ∀ K : ℝ,0≤K → ∀ k : ℕ,(∀ x,|φ x|≤K*(1+|x|^k)) →
          Tendsto (fun w : Window => mean (window q r w.start w.len) (fun p => φ ((S p:ℝ)/p-log p/2)))
            (windows θ) (𝓝 (∫ x,φ x ∂(law F hc)))

theorem original (h : DistributionInput) (hAP : ProgressionMangoldt) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : ClassLaw θ := by
  let β := (1/6+θ)/2
  have hh := ThetaAlmostPrimeCounts.limit (by linarith : 0<θ) (show β<θ by dsimp [β];linarith)
    (h β (by dsimp [β];linarith) (by dsimp [β];linarith))
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  exact ⟨nontrivial ht,F,hF,fun _ _ hq hr hu => ⟨positive hAP hq hr hu,weak hh hAP hq hr hu hF,
    fun _ hp _ hK k hg => test hh hAP hq hr hu hF hp hK k hg⟩⟩

#print axioms original
end
end Arxiv.«2501.03234».ThetaAlmostClassLaws
