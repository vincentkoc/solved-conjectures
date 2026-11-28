import ThetaClassPairProducts
import ThetaPairEmpirical
import ThetaProductTests

/-! The actual two-class prime-pair count and its own-count-normalized product law. -/
namespace Arxiv.«2501.03234».ThetaClassPairLaws
open Filter Finset Real MeasureTheory ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans
open ThetaAlmostPeriodicWindows ThetaAlmostPrimeDistribution ThetaConditionalHaar ThetaShortConditionalLaw
open ThetaIdentityFiber ThetaCharacterPrimeMeans ThetaNearbyPrimePairs ThetaClassPairProducts
open ThetaShortClassMeans ThetaLocalPrimeCounts
open scoped Topology BoundedContinuousFunction
noncomputable section

def selected (q r s t X H : ℕ) := (window q r X X).sigma (fun p => window s t p H)
def weight (q s : ℕ) : ℝ := 1/(q.totient:ℝ)*(1/(s.totient:ℝ))

theorem raw_eq (q r s t X H : ℕ) (u v : ℝ →ᵇ ℝ) :
    raw X H (mark q r u) (mark s t v)=
      ∑ z∈selected q r s t X H,u (residual z.1)*v (residual z.2) := by
  rw [selected,sum_sigma]
  change (∑ p∈sample X X,∑ l∈sample p H,mark q r u p*mark s t v l)=_
  simp_rw [←mul_sum]
  simp only [mark,mul_assoc]
  rw [weighted_sum]
  apply sum_congr rfl
  intro p _
  rw [weighted_sum]
  rfl

theorem pair_count {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r s t : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (hs : 0<s) (ht : t<s) (hv : t.Coprime s)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X : ℕ => (log X/X*(log X/H X))*((selected q r s t X (H X)).card:ℝ)) atTop
      (𝓝 (weight q s)) := by
  have hh := product_limit hθ hθ' h hAP hq hr hu hs ht hv hF (1 : ℝ →ᵇ ℝ) 1 hH
  simpa only [ThetaNearbyPrimePairs.factor,raw_eq,Pi.one_apply,BoundedContinuousFunction.coe_one,
    one_mul,mul_one,sum_const,nsmul_eq_mul,integral_const,probReal_univ,smul_eq_mul,weight] using hh

theorem weak {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r s t : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (hs : 0<s) (ht : t<s) (hv : t.Coprime s)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X => ThetaPairEmpirical.empirical (selected q r s t X (H X))) atTop
      (𝓝 ((law F (positive hAP hq hr hu)).prod (law F (positive hAP hs ht hv)))) := by
  have hq₀ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hs₀ : 0<(s.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hs
  have hd : 0<weight q s := by dsimp [weight];positivity
  have hc := pair_count hθ hθ' h hAP hq hr hu hs ht hv hF hH
  apply ThetaProductTests.weak
  intro u v
  have hp := product_limit hθ hθ' h hAP hq hr hu hs ht hv hF u v hH
  have L := hp.div hc hd.ne'
  rw [show ∀ a b : ℝ,(1/(q.totient:ℝ)*a)*(1/(s.totient:ℝ)*b)/weight q s=a*b by
    intro a b;rw [show _*_=weight q s*(a*b) by unfold weight;ring];exact mul_div_cancel_left₀ _ hd.ne'] at L
  rw [show ThetaProductTests.val ((law F (positive hAP hq hr hu)).prod (law F (positive hAP hs ht hv))) u v=_
    from integral_prod_mul u v]
  apply L.congr'
  filter_upwards [hc.eventually_const_lt hd] with X hx
  have hn : (selected q r s t X (H X)).Nonempty := by
    by_contra hh;rw [not_nonempty_iff_eq_empty.mp hh] at hx;simp at hx
  dsimp only [Pi.div_apply,ThetaProductTests.val]
  rw [ThetaNearbyPrimePairs.factor,raw_eq,ThetaPairEmpirical.integral_empirical (f:=fun z : ℝ×ℝ => u z.1*v z.2) hn
    ((u.continuous.measurable.comp measurable_fst).mul (v.continuous.measurable.comp measurable_snd))]
  exact mul_div_mul_left _ _ (left_ne_zero_of_mul hx.ne')

def ClassPairs (θ : ℝ) : Prop := ∃ F : G →₁[haar] ℝ,Represents residual F ∧
  ∀ q r s t : ℕ,0<q → r<q → r.Coprime q → 0<s → t<s → t.Coprime s →
  ∃ hc : haar (fibre q r)≠0,∃ hd : haar (fibre s t)≠0,∀ H : ℕ → ℕ,
    (∀ᶠ X : ℕ in atTop,Admits θ X (H X)) →
    Tendsto (fun X => ThetaPairEmpirical.empirical (selected q r s t X (H X))) atTop
      (𝓝 ((law F hc).prod (law F hd))) ∧
    Tendsto (fun X : ℕ => (log X/X*(log X/H X))*((selected q r s t X (H X)).card:ℝ)) atTop (𝓝 (weight q s))

theorem original (h : DistributionInput) (hAP : ProgressionMangoldt) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) :
    ClassPairs θ := by
  let β := (1/6+θ)/2
  have h₀ : 0<θ := by linarith
  have hh := ThetaAlmostPrimeCounts.limit h₀ (show β<θ by dsimp [β];linarith)
    (h β (by dsimp [β];linarith) (by dsimp [β];linarith))
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  exact ⟨F,hF,fun _ _ _ _ hq hr hu hs ht' hv => ⟨positive hAP hq hr hu,positive hAP hs ht' hv,
    fun _ hH => ⟨weak h₀ ht hh hAP hq hr hu hs ht' hv hF hH,pair_count h₀ ht hh hAP hq hr hu hs ht' hv hF hH⟩⟩⟩

#print axioms original
#print axioms pair_count
#print axioms weak
end
end Arxiv.«2501.03234».ThetaClassPairLaws
