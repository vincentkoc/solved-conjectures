import ThetaLocalPrimeMomentLimits

/-! A single fixed periodic predictor is accurate in prime mean square
simultaneously on all sufficiently late short intervals. -/
namespace Arxiv.«2501.03234».ThetaLocalPeriodicPrediction
open Real Filter Finset ThetaLocalPrimeCounts ThetaCharacterPrimeMeans ThetaPrimeLaw ThetaDiagonalConstant
open ThetaPrimeTailTransfer ThetaLocalDyadicReference ThetaLocalModelComparison ThetaPeriodMeans ThetaCalibratedCone
noncomputable section

theorem periodic_bound {q : ℕ} (hq : 0<q) {f : ℕ → ℝ} (hf : OnMod q f) :
    ∃ D : ℝ, 0≤D ∧ ∀ n,|f n|≤D := by
  refine ⟨∑ i∈range q,|f i|,sum_nonneg (fun _ _ => abs_nonneg _),fun n => ?_⟩
  rw [←hf n]
  exact single_le_sum (fun i _ => abs_nonneg (f i)) (mem_range.mpr (Nat.mod_lt n hq))

theorem global_square {ε : ℝ} (hε : 0<ε) : ∃ T V : ℕ, ∀ᶠ X : ℕ in atTop,
    (∑ p∈Nat.primesLE X,(residual p-residualModel T V p)^2)≤ε*X.primeCounting := by
  let c := 8/π^2
  have hc : 0<c := by dsimp [c];positivity
  obtain ⟨T,V,_,_,hmodel⟩ := prime_model_approximation (show 0<ε/(4*c^2) by positivity)
  refine ⟨T,V,?_⟩
  filter_upwards [hmodel,diagonal_square_error.eventually_le_const (show 0<ε/4 by positivity),
    Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ)] with X hm hd hx
  have hX : 0<(X.primeCounting:ℝ) := by exact_mod_cast hx
  let U (p : ℕ) := residual p-diagonalConstant-c*scaledOff p
  let W (p : ℕ) := scaledOff p-model T V p
  change (∑ p∈Nat.primesLE X,U p^2)/X.primeCounting≤ε/4 at hd
  have hh (p : ℕ) : (residual p-residualModel T V p)^2≤2*U p^2+2*c^2*W p^2 := by
    have heq : residual p-residualModel T V p=U p+c*W p := by dsimp [residualModel,U,W,c];ring
    rw [heq];nlinarith only [sq_nonneg (U p-c*W p)]
  apply (sum_le_sum (fun p _ => hh p)).trans
  rw [sum_add_distrib,← mul_sum,← mul_sum]
  have hh := mul_le_mul_of_nonneg_left hm (show 0≤2*c^2 by positivity)
  have heq : 2*c^2*(ε/(4*c^2)*X.primeCounting)=ε/2*X.primeCounting := by field_simp;ring
  rw [heq] at hh
  change 2*c^2*(∑ p∈Nat.primesLE X,W p^2)≤_ at hh
  linarith only [(div_le_iff₀ hX).mp hd,hh]

theorem original {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) {ε : ℝ} (hε : 0<ε) :
    ∃ T V : ℕ, ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      avg X H (fun p => (residual p-residualModel T V p)^2)≤ε := by
  obtain ⟨C,hC,hπ⟩ := pi_bound
  obtain ⟨T,V,hg⟩ := global_square (show 0<ε/(2*C) by positivity)
  let b := residualModel T V
  let w (p : ℕ) := -b p
  have hw : OnMod T.factorial w := fun p => congrArg Neg.neg (residualModel_periodic T V p)
  obtain ⟨D,_,hD⟩ := periodic_bound (Nat.factorial_pos _) hw
  have hc := ThetaLocalMomentComparison.original he h48 hk hθ hθ₁ h (Nat.factorial_pos T)
    (fun _ => (1:ℝ)) w (fun _ => rfl) hw (fun _ => by norm_num) hD 2 (half_pos hε)
  refine ⟨T,V,?_⟩
  filter_upwards [hπ,twice.eventually hg,hc,ThetaLocalMomentBudgets.count h,eventually_ge_atTop (1:ℕ)]
    with X hπ hglob hc hcnt hX
  have hmass := (hcnt X le_rfl (full_length hX hθ₁)).1
  let f (p : ℕ) := (residual p-b p)^2
  have hmean : avg X X f≤ε/2 := by
    rw [avg,div_le_iff₀ hmass]
    apply (sum_le_sum_of_subset_of_nonneg (fun _ hp => sample_sub hp (le_refl X)) (fun _ _ _ => sq_nonneg _)).trans
    apply hglob.trans
    apply (mul_le_mul_of_nonneg_left hπ (show 0≤ε/(2*C) by positivity)).trans_eq
    field_simp
  intro H hHX hlen
  have hh := hc H hHX hlen
  have eqf : (fun p : ℕ => (1:ℝ)*(w p+residual p)^2)=f := by funext p;dsimp [w,f];ring
  change |avg X H (fun p => 1*(w p+residual p)^2)-avg X X (fun p => 1*(w p+residual p)^2)|≤ε/2 at hh
  rw [eqf] at hh
  change avg X H f≤ε
  linarith only [(le_abs_self _).trans hh,hmean]

#print axioms global_square
#print axioms original
end
end Arxiv.«2501.03234».ThetaLocalPeriodicPrediction
