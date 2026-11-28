import ThetaPairComparison
import ThetaAlmostPrimeDistribution

/-! Product limits with the true unweighted number of directed prime pairs
in the denominator. The gap may be any integer up to the specified length. -/
namespace Arxiv.«2501.03234».ThetaNearbyPrimePairs
open Real Finset Filter MeasureTheory ThetaWindowApproximation ThetaAlmostPeriodicWindows
open ThetaLocalPrimeCounts ThetaPrimeStartDensity ThetaPrimeAnchorTests ThetaNaturalPrimeMeans
open ThetaProfiniteUnits ThetaPrimeLaw ThetaCharacterPrimeMeans ThetaAlmostPrimeDistribution
open ThetaPairComparison
open scoped Topology
noncomputable section

def raw (X H : ℕ) (f g : ℕ → ℝ) :=
  ∑ p∈sample X X,∑ r∈sample p H,f p*g r
def count (X H : ℕ) := ∑ p∈sample X X,(sample p H).card
def actual (X H : ℕ) (f g : ℕ → ℝ) := raw X H f g/count X H

theorem factor (X H : ℕ) (f g : ℕ → ℝ) :
    scaled X H f g = (log X/X*(log X/H))*raw X H f g := by
  simp only [scaled,avg,raw,←mul_sum]
  rw [mul_assoc]
  congr 1
  rw [mul_sum]
  exact sum_congr rfl (fun p _ => by ring)

theorem count_eq (X H : ℕ) : raw X H (fun _ => 1) (fun _ => 1)=(count X H:ℝ) := by
  simp [raw,count]

theorem product {θ : ℝ} (ht : 0<θ) (hAP : ProgressionMangoldt) {f g : ℕ → ℝ}
    {B D a b : ℝ} (hB : 0<B) (hf : ∀ p,|f p|≤B) (hD : 0≤D) (hg : ∀ p,|g p|≤D)
    (ha : Tendsto (primeMean f) atTop (𝓝 a))
    (hb : ∀ t : ℝ,0<t → Typical (fun X n => ∀ H : ℕ,Admits θ X H → |avg X n H g-b|≤t))
    {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X => scaled X (H X) f g) atTop (𝓝 (a*b)) := by
  have hh := (compare ht hAP hB hf hD hg hb hH).add ((ThetaPairDyadic.first hAP ha).mul_const b)
  simpa using hh

theorem ordinary {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt) :
    ∀ t : ℝ,0<t → Typical (fun X n => ∀ H : ℕ,Admits θ X H → |avg X n H (fun _ => (1:ℝ))-1|≤t) := by
  have hf : Approximable (fun _ => (1:ℝ)) := by
    intro ε he
    refine ⟨1,fun _ => 1,fun _ => rfl,Eventually.of_forall ?_⟩
    intro X;simp [primeMean,he.le]
  exact fun _ he => limit ht ht' h hAP (ThetaPrimeAnchorTransfer.bounded (B:=1) (fun _ => by norm_num))
    hf ThetaPairDyadic.ones he

theorem pair_mass {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X : ℕ => (log X/X*(log X/H X))*(count X (H X):ℝ)) atTop (𝓝 1) := by
  simpa only [factor,count_eq,mul_one] using product ht hAP (f:=fun _ => (1:ℝ)) (g:=fun _ => (1:ℝ))
    (by norm_num : (0:ℝ)<1) (fun _ => by norm_num) (by norm_num : (0:ℝ)≤1) (fun _ => by norm_num)
    ThetaPairDyadic.ones (ordinary ht ht' h hAP) hH

theorem averages {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {φ ψ : ℝ → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) {B D : ℝ} (hB : 0≤B) (hf : ∀ x,|φ x|≤B) (hD : 0≤D) (hg : ∀ x,|ψ x|≤D)
    {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X => actual X (H X) (fun p => φ (residual p)) (fun p => ψ (residual p))) atTop
      (𝓝 ((∫ x, φ x ∂(haarLaw F : Measure ℝ))*(∫ x, ψ x ∂(haarLaw F : Measure ℝ)))) := by
  have hp {g : ℝ → ℝ} {K : ℝ} (hk : 0≤K) (hg : ∀ x, |g x|≤K) (x : ℝ) : |g x|≤K*(1+|x|^0) := by
    rw [pow_zero];linarith only [hg x,hk]
  have h₁ := (ThetaResidualMoments.prime_polynomial_growth hAP hF hφ (hp hB hf)).2
  have h₂ := fun t (ht'' : 0<t) => polynomial ht ht' h hAP hF hψ hD 0 (hp hD hg) ht''
  have hh := product ht hAP (show 0<B+1 by linarith) (fun p => (hf (residual p)).trans (by linarith))
    hD (fun p => hg (residual p)) h₁ h₂ hH
  have hmass := pair_mass ht ht' h hAP hH
  have hlim := hh.div hmass one_ne_zero
  rw [div_one] at hlim
  apply hlim.congr'
  filter_upwards [hmass.eventually_const_lt (by norm_num : (0:ℝ)<1)] with X hX
  have hn := left_ne_zero_of_mul (ne_of_gt hX)
  simp only [factor,actual]
  exact mul_div_mul_left _ _ hn

#print axioms pair_mass
#print axioms averages
end
end Arxiv.«2501.03234».ThetaNearbyPrimePairs
