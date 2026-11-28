import ThetaPairMomentBounds
import ThetaPairTestTruncation

/-! Polynomial-growth joint observables on actual nearby prime pairs with two
independently prescribed reduced classes. -/
namespace Arxiv.«2501.03234».ThetaClassPairMoments
open Filter Finset Real MeasureTheory ThetaClassPairLaws ThetaPairMomentBounds ThetaPairTestTruncation
open ThetaPairEmpirical ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaConditionalHaar
open ThetaShortConditionalLaw ThetaCharacterPrimeMeans ThetaAlmostPeriodicWindows
open ThetaAlmostPrimeDistribution
open scoped Topology
noncomputable section

private theorem growth (k : ℕ) (x : ℝ) : |(|x|^k)|≤1*(1+|x|^k) := by
  rw [abs_of_nonneg (by positivity : 0≤|x|^k),one_mul];linarith

private theorem square {φ : ℝ×ℝ → ℝ} {K : ℝ} {k : ℕ}
    (hg : ∀ z : ℝ×ℝ,|φ z|≤K*(1+|z.1|^k+|z.2|^k)) (z : ℝ×ℝ) :
    (φ z)^2≤3*K^2*(1+|z.1|^(k*2)+|z.2|^(k*2)) := by
  let x := |z.1|^k
  let y := |z.2|^k
  have hb := pow_le_pow_left₀ (abs_nonneg _) (hg z) 2
  rw [sq_abs,mul_pow] at hb
  simp only [pow_mul]
  change _≤3*K^2*(1+x^2+y^2)
  change (φ z)^2≤K^2*(1+x+y)^2 at hb
  have h : (1+x+y)^2≤3*(1+x^2+y^2) := by nlinarith only [sq_nonneg (1-x),sq_nonneg (1-y),sq_nonneg (x-y)]
  nlinarith only [hb,mul_le_mul_of_nonneg_left h (sq_nonneg K)]

theorem tests {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r s t : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (hs : 0<s) (ht : t<s) (hv : t.Coprime s)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X))
    {φ : ℝ×ℝ → ℝ} (hp : Continuous φ) {K : ℝ} (k : ℕ) (hg : ∀ z : ℝ×ℝ,|φ z|≤K*(1+|z.1|^k+|z.2|^k)) :
    Tendsto (fun X => ∫ z,φ z ∂(empirical (selected q r s t X (H X)))) atTop
      (𝓝 (∫ z,φ z ∂((law F (positive hAP hq hr hu)).prod (law F (positive hAP hs ht hv))))) := by
  let μ := law F (positive hAP hq hr hu)
  let ν := law F (positive hAP hs ht hv)
  have powlim (l : ℕ) := ThetaResidualMoments.prime_polynomial_growth hAP hF
    (show Continuous (fun x : ℝ => |x|^l) by fun_prop) (growth l)
  have hi₁ := ThetaShortConditionalTests.integrable F (positive hAP hq hr hu) (by fun_prop) (powlim k).1
  have hi₂ := ThetaShortConditionalTests.integrable F (positive hAP hs ht hv) (by fun_prop) (powlim k).1
  have hint := (integrable_const (μ:=(μ:Measure ℝ).prod (ν:Measure ℝ)) (1:ℝ)).add (hi₁.comp_fst (ν:Measure ℝ))
  have hdom := (hint.add (hi₂.comp_snd (μ:Measure ℝ))).const_mul K
  have hi : Integrable φ ((μ:Measure ℝ).prod (ν:Measure ℝ)) :=
    hdom.mono' hp.aestronglyMeasurable (Eventually.of_forall (fun z => hg z))
  obtain ⟨B,hB,huv⟩ := budgets hθ hθ' h hAP hq hr hu hs ht hv hF hH
    (show ∀ p : ℕ,0≤|residual p|^(k*2) by intro p;positivity) (powlim (k*2)).2
  apply ThetaPairTestTruncation.limit (μ:=μ.prod ν) hp hi (weak hθ hθ' h hAP hq hr hu hs ht hv hF hH)
    (B:=3*K^2*(1+B+B)) (by positivity)
  filter_upwards [huv] with X hx
  let Z := selected q r s t X (H X)
  obtain ⟨hn,h₁,h₂⟩ := hx
  refine ⟨hn,?_⟩
  have hz : 0<(Z.card:ℝ) := by exact_mod_cast hn.card_pos
  have h₃ := sum_le_sum (s:=Z) (fun z _ => square hg (observe z))
  simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at h₃
  dsimp only [observe] at h₃
  rw [div_le_iff₀ hz] at h₁ h₂ ⊢
  have ha := add_le_add h₁ h₂
  dsimp only [Z,observe] at h₃ ha ⊢
  nlinarith only [h₃,mul_le_mul_of_nonneg_left ha (by positivity : 0≤3*K^2)]

private theorem monomial (m n : ℕ) (z : ℝ×ℝ) :
    |z.1^m*z.2^n|≤1*(1+|z.1|^(m+n)+|z.2|^(m+n)) := by
  rw [abs_mul,abs_pow,abs_pow,one_mul]
  let M := max |z.1| |z.2|
  have h₁ := pow_le_pow_left₀ (abs_nonneg z.1) (le_max_left |z.1| |z.2|) m
  have h₂ := pow_le_pow_left₀ (abs_nonneg z.2) (le_max_right |z.1| |z.2|) n
  have ht : |z.1|^m*|z.2|^n≤M^(m+n) := by
    rw [pow_add];exact mul_le_mul h₁ h₂ (by positivity) (by dsimp [M];positivity)
  apply ht.trans
  rcases le_total |z.1| |z.2| with h|h
  · dsimp only [M];rw [max_eq_right h];linarith only [pow_nonneg (abs_nonneg z.1) (m+n)]
  · dsimp only [M];rw [max_eq_left h];linarith only [pow_nonneg (abs_nonneg z.2) (m+n)]

theorem mixed {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r s t : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (hs : 0<s) (ht : t<s) (hv : t.Coprime s)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X))
    (m n : ℕ) :
    Tendsto (fun X => ∫ z : ℝ×ℝ,z.1^m*z.2^n ∂(empirical (selected q r s t X (H X)))) atTop
      (𝓝 ((∫ x : ℝ,x^m ∂(law F (positive hAP hq hr hu)))*(∫ y : ℝ,y^n ∂(law F (positive hAP hs ht hv))))) := by
  have hh := tests hθ hθ' h hAP hq hr hu hs ht hv hF hH (by fun_prop) (m+n) (monomial m n)
  rw [ProbabilityMeasure.toMeasure_prod,integral_prod_mul (fun x : ℝ => x^m) (fun y : ℝ => y^n)] at hh
  exact hh

def PolynomialPairs (θ : ℝ) : Prop := ∃ F : G →₁[haar] ℝ,Represents residual F ∧
  ∀ q r s t : ℕ,0<q → r<q → r.Coprime q → 0<s → t<s → t.Coprime s →
  ∃ hc : haar (fibre q r)≠0,∃ hd : haar (fibre s t)≠0,∀ H : ℕ → ℕ,
    (∀ᶠ X : ℕ in atTop,Admits θ X (H X)) → ∀ φ : ℝ×ℝ → ℝ,Continuous φ → ∀ K : ℝ,∀ k : ℕ,
    (∀ z : ℝ×ℝ,|φ z|≤K*(1+|z.1|^k+|z.2|^k)) →
    Tendsto (fun X => ∫ z,φ z ∂(empirical (selected q r s t X (H X)))) atTop
      (𝓝 (∫ z,φ z ∂((law F hc).prod (law F hd))))

theorem original (h : DistributionInput) (hAP : ProgressionMangoldt) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) :
    PolynomialPairs θ := by
  let β := (1/6+θ)/2
  have h₀ : 0<θ := by linarith
  have hh := ThetaAlmostPrimeCounts.limit h₀ (show β<θ by dsimp [β];linarith)
    (h β (by dsimp [β];linarith) (by dsimp [β];linarith))
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  exact ⟨F,hF,fun _ _ _ _ hq hr hu hs ht' hv => ⟨positive hAP hq hr hu,positive hAP hs ht' hv,
    fun _ hH _ hp _ k hg => tests h₀ ht hh hAP hq hr hu hs ht' hv hF hH hp k hg⟩⟩

#print axioms original
#print axioms mixed

#print axioms tests
end
end Arxiv.«2501.03234».ThetaClassPairMoments
