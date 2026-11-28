import ThetaNearbyPrimePairs
import ThetaPairDyadic

/-! True prime-count normalization for polynomial-growth tests in windows
starting at a typical prime, simultaneously in all admissible lengths. -/
namespace Arxiv.«2501.03234».ThetaPrimeStartMoments
open Real Filter Finset MeasureTheory ThetaNaturalPrimeMeans ThetaLocalPrimeCounts
open ThetaAlmostPeriodicWindows ThetaWindowApproximation ThetaPrimeStartDensity ThetaCharacterPrimeMeans
open ThetaPrimeLaw ThetaProfiniteUnits
open scoped Topology
noncomputable section

private theorem both {P Q R : ℕ → ℕ → Prop} (hp : Typical P) (hq : Typical Q)
    (hm : ∀ᶠ X : ℕ in atTop,∀ n,P X n → Q X n → R X n) : Typical R := by
  classical
  intro ε he
  filter_upwards [hp (ε/2) (half_pos he),hq (ε/2) (half_pos he),hm,eventually_ge_atTop (1:ℕ)] with X ha hb h hx
  have hs : missed X (R X)⊆missed X (P X)∪missed X (Q X) := by
    intro n hn
    obtain ⟨hn,hr⟩ := mem_missed.mp hn
    by_cases hv : P X n
    · exact mem_union_right _ (mem_missed.mpr ⟨hn,fun hq => hr (h n hv hq)⟩)
    · exact mem_union_left _ (mem_missed.mpr ⟨hn,hv⟩)
  have hc := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card hs).trans (card_union_le ..))
  push_cast at hc
  linarith only [mul_le_mul_of_nonneg_right hc (log_nonneg (Nat.one_le_cast.mpr hx)),ha,hb]

theorem normalized {θ : ℝ} (ht : 0<θ) (ht' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {K : ℝ} (hK : 0≤K) (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k)) {ε : ℝ} (he : 0<ε) :
    Typical (fun X n => ∀ H : ℕ,Admits θ X H →
      |ThetaShortResidualLaw.actual n H (fun p => φ (residual p))-(∫ x, φ x ∂(haarLaw F:Measure ℝ))|≤ε) := by
  let a := ∫ x, φ x ∂(haarLaw F:Measure ℝ)
  let t := min (1/4) (ε/(4*(|a|+1)))
  have ht₀ : 0<t := lt_min (by norm_num) (by positivity)
  have ht₁ : t≤1/4 := min_le_left ..
  have ht₂ : t*(4*(|a|+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  apply both (ThetaPrimeAnchorTests.polynomial ht ht' h hAP hF hφ hK k hg ht₀)
    (ThetaNearbyPrimePairs.ordinary ht ht' h hAP t ht₀)
  filter_upwards with X
  intro n hv hm H hH
  let u := avg X n H (fun p => φ (residual p))
  let m := avg X n H (fun _ => 1)
  have hu : |u-a|≤t := hv H hH
  have hc : |m-1|≤t := hm H hH
  have hm' : 1/2 ≤ m := by linarith only [(abs_le.mp hc).1,ht₁]
  have hm₀ : 0 < m := by linarith
  have eqn : ThetaShortResidualLaw.actual n H (fun p => φ (residual p))=u/m := by
    have hn := hm₀.ne'
    simp only [m,avg,sum_const,nsmul_eq_mul,mul_one] at hn
    simp only [u,m,avg,ThetaShortResidualLaw.actual,sum_const,nsmul_eq_mul,mul_one,mul_div_mul_left _ _ (left_ne_zero_of_mul hn)]
  rw [eqn]
  change |u/m-a|≤ε
  rw [show u/m-a=(u-a*m)/m by field_simp,abs_div,abs_of_pos hm₀,div_le_iff₀ hm₀]
  have herr : |u-a*m|≤t+|a| * t := calc
    _ = |(u-a)-a*(m-1)| := by ring_nf
    _ ≤ |u-a|+|a*(m-1)| := abs_sub ..
    _ ≤ _ := by rw [abs_mul];exact add_le_add hu (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
  nlinarith only [herr,ht₂,mul_le_mul_of_nonneg_left hm' he.le,he]

#print axioms normalized
end
end Arxiv.«2501.03234».ThetaPrimeStartMoments
