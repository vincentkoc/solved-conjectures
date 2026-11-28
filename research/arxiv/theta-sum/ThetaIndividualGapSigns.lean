import ThetaCompatibleSignedGaps

/-! Individual positive and negative displacements for the original arithmetic
sum, up to any threshold strictly below its mean on compatible gaps. -/
namespace Arxiv.«2501.03234».ThetaIndividualGapSigns
open Filter Finset Real ThetaCompatibleSignedGaps ThetaFrequentSignedGaps ThetaSignedGapEnergy
open ThetaGapBiasThree ThetaGapFibres ThetaCharacterCoefficient ThetaPopularLagCounts
open ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans
open ThetaAlmostPeriodicWindows ThetaAlmostPrimeDistribution
open scoped Topology
noncomputable section

def coefficient (d : ℕ) := if d=0 then characterConstant^2/2 else characterConstant^2/4
def hits (d X H : ℕ) (b : ℝ) := (compatible d H).filter (fun l => b≤oriented d X H l)

def Statement (θ : ℝ) : Prop := 0<characterConstant ∧ ∀ d : ℕ,d<3 → ∀ b : ℝ,0≤b → b<6*coefficient d →
  ∃ η : ℝ,0<η ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,Admits θ X H → η*H≤((hits d X H b).card:ℝ)

theorem original (h : DistributionInput) (hAP : ProgressionMangoldt) (U : Upper)
    {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : Statement θ := by
  let β := (1/6+θ)/2
  have h₀ : 0<θ := by linarith
  have hh := ThetaAlmostPrimeCounts.limit h₀ (show β<θ by dsimp [β];linarith)
    (h β (by dsimp [β];linarith) (by dsimp [β];linarith))
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  obtain ⟨D,hD,hen⟩ := energy h₀ ht hh hAP U hF
  obtain ⟨hC,hgap⟩ := ThetaGapBiasThree.original h hAP hθ ht
  refine ⟨hC,?_⟩
  intro d hd b hb ht'
  let s := (coefficient d-b/6)/4
  let g := b/6+2*s
  have hs : 0<s := by dsimp [s];linarith only [ht']
  have hg : g<coefficient d := by dsimp [g,s];linarith only [ht']
  refine ⟨s^2/(4*(2*D+2*b^2)),by positivity,lengths ht ?_⟩
  intro H hH
  obtain ⟨_,w,_⟩ := hgap H hH
  have lim : Tendsto (fun X => (∑ l∈shifts d (H X),oriented d X (H X) l)/(H X)) atTop (𝓝 (coefficient d)) := by
    simp only [ThetaFrequentSignedGaps.mean,coefficient]
    interval_cases d
    · simpa using w.1
    · simpa only [show ¬(1:ℕ)=0 by decide,if_false,neg_div,neg_neg,Pi.neg_apply] using w.2.1.neg
    · simpa only [show ¬(2:ℕ)=0 by decide,if_false,neg_div,neg_neg,Pi.neg_apply] using w.2.2.neg
  have grows := (tendsto_rpow_atTop h₀).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),hH,hen _ hH,lim.eventually_const_lt hg,
    grows.eventually_ge_atTop (b/s)] with X hx hh he hm hsize
  have hl : 0<(H X:ℝ) := by exact_mod_cast hh.1
  have hbig := (div_le_iff₀ hs).mp ((show b/s≤(X:ℝ)^θ from hsize).trans hh.2.2)
  have hsq : (∑ l∈shifts d (H X),(oriented d X (H X) l)^2)≤D*(H X) := by
    by_cases h : d=0 <;> simpa [oriented,h] using he d
  exact select_at hx hh.1 hb hs hD le_rfl (by linarith only [hbig]) ((lt_div_iff₀ hl).mp hm).le hsq

#print axioms original
end
end Arxiv.«2501.03234».ThetaIndividualGapSigns
