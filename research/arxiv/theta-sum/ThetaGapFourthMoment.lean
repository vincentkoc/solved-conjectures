import ThetaGapFibres

/-! Total fourth moment of the centered products over all nearby prime pairs. -/
namespace Arxiv.«2501.03234».ThetaGapFourthMoment
open Filter Finset Real MeasureTheory ThetaPairEmpirical ThetaGapBiasThree ThetaPairBiasThree
open ThetaClassPairLaws ThetaClassPairMoments ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans
open ThetaCharacterPrimeMeans ThetaShortConditionalLaw ThetaConditionalHaar ThetaDiagonalConstant
open ThetaAlmostPeriodicWindows ThetaShortClassMeans
open scoped Topology
noncomputable section

def densityScale (X : ℕ) := (log X)^2/X

theorem scale_eq (X H : ℕ) : scale X H=densityScale X/H := by unfold scale densityScale;ring

private theorem growth (z : ℝ×ℝ) :
    |(test z)^4|≤(1+|diagonalConstant|)^8*(1+|z.1|^8+|z.2|^8) := by
  have a := ThetaResidualMoments.centered_growth diagonalConstant 8 z.1
  have b := ThetaResidualMoments.centered_growth diagonalConstant 8 z.2
  rw [abs_of_nonneg (by positivity : 0≤(z.1-diagonalConstant)^8)] at a
  rw [abs_of_nonneg (by positivity : 0≤(z.2-diagonalConstant)^8)] at b
  rw [abs_of_nonneg (by positivity),test,mul_pow]
  dsimp only [ThetaPairBiasThree.center]
  have h := sq_nonneg ((z.1-diagonalConstant)^4-(z.2-diagonalConstant)^4)
  nlinarith only [a,b,h,mul_nonneg (by positivity : 0≤(1+|diagonalConstant|)^8)
    (add_nonneg (by positivity : 0≤|z.1|^8) (by positivity : 0≤|z.2|^8))]

private theorem all (X H : ℕ) : selected 1 0 1 0 X H=pairs X H := by
  ext z
  simp only [selected,pairs,window,ThetaLocalIntervalTests.cell,mem_sigma,mem_filter,Nat.mod_one,and_true]

theorem bound {θ : ℝ} (hθ : 0<θ) (ht : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) : ∃ B : ℝ,0<B ∧ ∀ H : ℕ → ℕ,
    (∀ᶠ X : ℕ in atTop,Admits θ X (H X)) → ∀ᶠ X : ℕ in atTop,
      densityScale X*(∑ z∈pairs X (H X),(test (ThetaPairTestTruncation.observe z))^4)≤B*(H X) := by
  let v (z : ℝ×ℝ) := (test z)^4
  have hv : Continuous v := by dsimp [v,test,ThetaPairBiasThree.center];fun_prop
  let μ := law F (positive hAP (q:=1) (r:=0) (by decide) (by decide) (by decide))
  let a := ∫ z,v z ∂(μ.prod μ)
  refine ⟨|a|+1,by positivity,?_⟩
  intro H hH
  have L := tests hθ ht h hAP (q:=1) (r:=0) (s:=1) (t:=0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hF hH hv 8 growth
  simp only [all] at L
  have hc := ThetaNearbyPrimePairs.pair_mass hθ ht h hAP hH
  have hx := hc.mul L
  rw [one_mul] at hx
  filter_upwards [hx.eventually_lt_const (show a < |a|+1 by linarith only [le_abs_self a]),hH,
    hc.eventually_const_lt (by norm_num : (0:ℝ)<1)] with X he hh hm
  have hn : (pairs X (H X)).Nonempty := by
    apply card_pos.mp
    rw [size];by_contra! hz;rw [Nat.le_zero.mp hz] at hm;simp at hm
  have hz : ((pairs X (H X)).card:ℝ)≠0 := by exact_mod_cast hn.card_pos.ne'
  change scale X (H X)*(ThetaNearbyPrimePairs.count X (H X):ℝ)*(∫ z,v z ∂(empirical (pairs X (H X))))<_ at he
  rw [←size,integral_empirical hn hv.measurable,mul_assoc,mul_div_cancel₀ _ hz,scale_eq] at he
  have hl : 0<(H X:ℝ) := by exact_mod_cast hh.1
  rw [div_mul_eq_mul_div,div_lt_iff₀ hl] at he
  exact he.le

#print axioms bound
end
end Arxiv.«2501.03234».ThetaGapFourthMoment
