import ThetaLagMomentDispersion
import ThetaGapFourthMoment

/-! A uniform square-mean bound for the scaled signed product at individual
prime displacements, including the unbounded original theta residuals. -/
namespace Arxiv.«2501.03234».ThetaSignedGapEnergy
open Filter Finset Real MeasureTheory ThetaGapFourthMoment ThetaGapFibres ThetaLagMomentDispersion
open ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaConditionalHaar ThetaCharacterPrimeMeans
open ThetaAlmostPeriodicWindows ThetaPopularLagCounts ThetaPositiveLag ThetaLagSieveWeights
open ThetaPairBiasThree ThetaGapBiasThree ThetaPairEmpirical ThetaPairTestTruncation
open scoped Topology
noncomputable section

theorem cube (U : Upper) : ∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,0<H → H≤X → ∀ d : ℕ,
    (∑ h∈shifts d H,(densityScale X*((fibre X H h).card:ℝ))^3)≤A*H := by
  obtain ⟨C,hC,hU⟩ := U
  refine ⟨2*(4*C)^3*exp 64,by positivity,?_⟩
  have h4 : Tendsto (fun X : ℕ => 4*X) atTop atTop := tendsto_atTop_mono (fun x => by change x≤4*x;omega) tendsto_id
  filter_upwards [h4.eventually hU,eventually_ge_atTop (2:ℕ)] with X hX hx
  intro H hH hHX d
  have hx' : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_nonneg (show 1≤(X:ℝ) by exact_mod_cast (show 1≤X by omega))
  have hl' := log_le_log hx' (show (X:ℝ)≤4*(X:ℝ) by linarith)
  have hw (h : ℕ) (hh : h∈shifts d H) : densityScale X*((fibre X H h).card:ℝ)≤4*C*weight 3 h := by
    obtain ⟨hh₁,hh₂⟩ := mem_Icc.mp (mem_filter.mp hh).1
    have hu := hX h (by omega) (by omega)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hu
    have ha : ((fibre X H h).card:ℝ)≤((ThetaDistinctPrimeQuadruples.pairs (4*X) h).card:ℝ) := by exact_mod_cast inject hHX
    have hb := mul_le_mul ha (pow_le_pow_left₀ hl hl' 2) (sq_nonneg _) (Nat.cast_nonneg _)
    dsimp [densityScale]
    rw [div_mul_eq_mul_div,div_le_iff₀ hx']
    linarith only [hb,hu]
  have hs : shifts d H⊆offsets (H+1) := by
    intro h hh
    obtain ⟨ha,hb⟩ := mem_Icc.mp (mem_filter.mp hh).1
    exact mem_erase.mpr ⟨by omega,mem_range.mpr (by omega)⟩
  have hb := (sum_le_sum_of_subset_of_nonneg hs (fun h _ _ => pow_nonneg (nonneg (by norm_num : (0:ℝ)≤3) h) 3)).trans (weight_cube (H+1))
  have hh' := sum_le_sum (s:=shifts d H) (fun h hh => pow_le_pow_left₀ (by dsimp [densityScale];positivity) (hw h hh) 3)
  simp only [mul_pow,←mul_sum] at hh'
  have hHr : (1:ℝ)≤H := by exact_mod_cast hH
  simp only [Nat.cast_add,Nat.cast_one] at hb
  simp only [mul_pow,←mul_sum]
  apply hh'.trans
  nlinarith only [mul_le_mul_of_nonneg_left hb (by positivity : 0≤(4*C)^3),
    mul_le_mul_of_nonneg_left hHr (by positivity : 0≤(4*C)^3*exp 64)]

def score (X H h : ℕ) := densityScale X*ThetaGapFibres.value X H h test

theorem energy {θ : ℝ} (hθ : 0<θ) (ht : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    (U : Upper) {F : G →₁[haar] ℝ} (hF : Represents residual F) : ∃ D : ℝ,0<D ∧ ∀ H : ℕ → ℕ,
    (∀ᶠ X : ℕ in atTop,Admits θ X (H X)) → ∀ᶠ X : ℕ in atTop,∀ d : ℕ,
      (∑ l∈shifts d (H X),(score X (H X) l)^2)≤D*(H X) := by
  obtain ⟨A,hA,ha⟩ := cube U
  obtain ⟨B,hB,hb⟩ := bound hθ ht h hAP hF
  refine ⟨sqrt (A*B),by positivity,?_⟩
  intro H hH
  filter_upwards [hb H hH,ha,hH] with X hv hdeg hh
  intro d
  let I := shifts d (H X)
  let w (z : Σ _ : ℕ,ℕ) := test (observe z)
  let ρ := densityScale X
  have hρ : 0≤ρ := by dsimp [ρ,densityScale];positivity
  have h₁ := hdeg (H X) hh.1 hh.2.1 d
  simp only [mul_pow,←mul_sum] at h₁
  have h₂ : ρ*(∑ l∈I,∑ z∈fibre X (H X) l,(w z)^4)≤B*(H X) := by
    have he := group d X (H X) (fun z => (test z)^4)
    change (∑ l∈I,∑ z∈fibre X (H X) l,(w z)^4)=_ at he
    rw [he]
    apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ (pairs X (H X)))
      (show ∀ z∈pairs X (H X),z∉gap d X (H X) → 0≤(w z)^4 by intro z _ _;positivity)) hρ) hv
  have hs := ThetaLagMomentDispersion.dispersion I (fibre X (H X)) w
  have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  apply (sq_le_sq₀ (sum_nonneg (fun l _ => sq_nonneg _)) (by positivity)).mp
  simp only [score,mul_pow,←mul_sum,Real.sq_sqrt (mul_nonneg hA.le hB.le)]
  change (ρ^2)^2*(∑ l∈I,(∑ z∈fibre X (H X) l,w z)^2)^2≤A*B*(H X:ℝ)^2
  dsimp only [I,ρ] at *
  nlinarith only [h₃,mul_le_mul_of_nonneg_left hs (by positivity : 0≤(densityScale X)^4)]

#print axioms cube
#print axioms energy
end
end Arxiv.«2501.03234».ThetaSignedGapEnergy
