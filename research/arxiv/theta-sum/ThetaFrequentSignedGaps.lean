import ThetaSignedGapEnergy

/-! Both signs of the original centered product occur at a positive fraction
of individual prime gaps. The gap residue modulo three determines the sign. -/
namespace Arxiv.«2501.03234».ThetaFrequentSignedGaps
open Filter Finset Real ThetaGapFibres ThetaSignedGapEnergy ThetaGapBiasThree ThetaPairBiasThree
open ThetaGapFourthMoment ThetaCharacterCoefficient ThetaPopularLagCounts ThetaAlmostPeriodicWindows
open ThetaNaturalPrimeMeans ThetaPrimeLaw ThetaProfiniteUnits ThetaCharacterPrimeMeans
open scoped Topology
noncomputable section

def oriented (d X H h : ℕ) := if d=0 then score X H h else -score X H h
def popular (d X H : ℕ) := (shifts d H).filter (fun h => characterConstant^2/16≤oriented d X H h)

theorem mean (X H d : ℕ) :
    (∑ h∈shifts d H,oriented d X H h)/H =
      if d=0 then scale X H*total (gap d X H) test else -(scale X H*total (gap d X H) test) := by
  by_cases hd : d=0 <;> simp only [oriented,hd,if_true,if_false,score,sum_neg_distrib,←mul_sum,
    group,scale_eq,neg_div] <;> ring

theorem lengths {θ : ℝ} (ht : θ≤1) {P : ℕ → ℕ → Prop}
    (h : ∀ H : ℕ → ℕ,(∀ᶠ X : ℕ in atTop,Admits θ X (H X)) → ∀ᶠ X : ℕ in atTop,P X (H X)) :
    ∀ᶠ X : ℕ in atTop,∀ H : ℕ,Admits θ X H → P X H := by
  classical
  let Bad (X : ℕ) := ∃ H,Admits θ X H ∧ ¬P X H
  let len (X : ℕ) := if e : Bad X then e.choose else X
  have admissible : ∀ᶠ X : ℕ in atTop,Admits θ X (len X) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with X hx
    dsimp only [len]
    split_ifs with e
    · exact e.choose_spec.1
    · exact ⟨hx,le_rfl,by simpa using rpow_le_rpow_of_exponent_le (show 1≤(X:ℝ) by exact_mod_cast hx) ht⟩
  filter_upwards [h _ admissible] with X hx
  intro H hH
  by_contra hn
  have e : Bad X := ⟨H,hH,hn⟩
  exact e.choose_spec.2 (by simpa [len,e] using hx)

theorem original (h : ThetaAlmostPrimeDistribution.DistributionInput) (hAP : ProgressionMangoldt)
    (U : Upper) {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) :
    0<characterConstant ∧ ∃ η : ℝ,0<η ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,Admits θ X H →
      ∀ d : ℕ,d<3 → η*H≤((popular d X H).card:ℝ) := by
  let β := (1/6+θ)/2
  have h₀ : 0<θ := by linarith
  have hh := ThetaAlmostPrimeCounts.limit h₀ (show β<θ by dsimp [β];linarith)
    (h β (by dsimp [β];linarith) (by dsimp [β];linarith))
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  obtain ⟨D,hD,hen⟩ := energy h₀ ht hh hAP U hF
  obtain ⟨hC,hgap⟩ := ThetaGapBiasThree.original h hAP hθ ht
  let c := characterConstant^2/8
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨hC,c^2/(4*D),by positivity,lengths ht ?_⟩
  intro H hH
  obtain ⟨_,w,_⟩ := hgap H hH
  have h₁ := w.1.eventually_const_lt (show c<characterConstant^2/2 by dsimp [c];nlinarith only [sq_pos_of_pos hC])
  have h₂ := w.2.1.neg.eventually_const_lt (show c< -(-(characterConstant^2)/4) by dsimp [c];nlinarith only [sq_pos_of_pos hC])
  have h₃ := w.2.2.neg.eventually_const_lt (show c< -(-(characterConstant^2)/4) by dsimp [c];nlinarith only [sq_pos_of_pos hC])
  filter_upwards [hH,hen H hH,h₁,h₂,h₃] with X hh he hp hm hn
  intro d hd
  have hsize := ThetaGapFibres.size (d:=d) (H:=H X)
  have hl : 0<(H X:ℝ) := by exact_mod_cast hh.1
  have hsum : c*(H X)≤∑ l∈shifts d (H X),oriented d X (H X) l := by
    apply (le_div_iff₀ hl).mp
    rw [mean]
    interval_cases d
    · exact hp.le
    · exact hm.le
    · exact hn.le
  have hsq : (∑ l∈shifts d (H X),(oriented d X (H X) l)^2)≤D*(H X) := by
    by_cases h : d=0 <;> simpa [oriented,h] using he d
  have Hsel := select hh.1 hsize (oriented d X (H X)) hc hD hsum hsq
  simpa only [popular,show c/2=characterConstant^2/16 by dsimp [c];ring] using Hsel

#print axioms original
end
end Arxiv.«2501.03234».ThetaFrequentSignedGaps
