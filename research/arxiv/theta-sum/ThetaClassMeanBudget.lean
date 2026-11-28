import ThetaDivisorBudget
import ThetaUniformClassMeans
import ThetaCompatibleMeans
import ThetaLargeLawTails

/-! Sharp maximum signed class means under a bound on the modulus. -/
namespace Arxiv.«2501.03234».ThetaClassMeanBudget
open Filter Real ThetaNaturalPrimeMeans ThetaProgressionProjection ThetaUniformClassMeans
open ThetaDivisorLogMean ThetaFactorialSequence
open scoped Topology
noncomputable section

/-- One absolute constant bounds every centered class mean under the period budget. -/
theorem upper (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0< C ∧ ∀ᶠ M : ℕ in atTop, ∀ m r : ℕ, [NeZero m] →
      m≤ M → r< m → r.Coprime m → |predictor m r|≤ C*(log (log M))^2 := by
  let c := ThetaUniformClassMeans.constant
  let K := |c|+1
  have hK : 0< K := by dsimp [K]; positivity
  refine ⟨952*K,by positivity,?_⟩
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have htt := tendsto_log_atTop.comp ht
  filter_upwards [ht.eventually_ge_atTop 2,htt.eventually_ge_atTop (max 1 (log 2))] with M hl hll
  change 2≤log (M:ℝ) at hl
  let y := ⌈log (M:ℝ)⌉₊
  have hy : log M≤ (y:ℝ) := Nat.le_ceil _
  have hly : log (log M)≤ log y := Real.log_le_log (by linarith only [hl] : 0< log M) hy
  have h1 : 1≤ log (log M) := (le_max_left ..).trans hll
  have h2 : log 2≤ log (log M) := (le_max_right ..).trans hll
  have hy' : 0< y := by exact_mod_cast (by linarith only [hl,hy] : 0<(y:ℝ))
  have hceil := Nat.ceil_lt_add_one (by linarith only [hl] : 0≤ log M)
  have hyu : log y≤ 2*log (log M) := by
    have h := Real.log_le_log (Nat.cast_pos.mpr hy') (show (y:ℝ)≤ 2*log M by dsimp [y]; linarith only [hl,hceil])
    rw [Real.log_mul (by norm_num) (by linarith only [hl] : log M≠0)] at h
    linarith
  intro m r _ hm hr hc
  have hM := Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos m)) (Nat.cast_le.mpr hm : (m:ℝ)≤ M)
  have hD := (ThetaDivisorBudget.bounds (NeZero.pos m) hy' (hM.trans hy) (h1.trans hly)).2
  have hcK : c≤ K := by dsimp [K]; linarith [le_abs_self c]
  have hL : 0≤ logMass m := Finset.sum_nonneg fun i _ => ThetaSmoothRows.logWeight_nonneg i
  have H := ThetaUniformClassMeans.bound hAP hr hc
  change _≤ c*logMass m at H
  have hg := mul_le_mul hcK hD hL hK.le
  have hsq := pow_le_pow_left₀ (by linarith only [h1,hly] : 0≤ log y) hyu 2
  nlinarith only [H,hg,mul_le_mul_of_nonneg_left hsq hK.le]

private lemma choose_parameter (P : ℕ → Prop) (H : ∀ᶠ T : ℕ in atTop,P T) :
    ∀ᶠ M : ℕ in atTop, ∃ T, P T ∧ modulus T≤ M ∧ log (log M)/8≤ log T ∧ 0≤ log (log M) := by
  let L (M : ℕ) := log (log M)
  let u (M : ℕ) := exp ((1/4)*L M)
  let t (M : ℕ) := ⌊u M⌋₊
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hL : Tendsto L atTop atTop := tendsto_log_atTop.comp hl
  have hu : Tendsto u atTop atTop := tendsto_exp_atTop.comp
    ((tendsto_const_mul_atTop_of_pos (by norm_num : 0<(1/4:ℝ))).mpr hL)
  have ht : Tendsto t atTop atTop := tendsto_nat_floor_atTop.comp hu
  filter_upwards [ht.eventually H,hL.eventually_ge_atTop (max 0 (8*log 2)),hl.eventually_gt_atTop 0,
    ht.eventually_ge_atTop 1] with M hp h₁ h₂ h₃
  let T := t M
  have hT : 0< T := h₃
  have hpos : 0<(T:ℝ) := Nat.cast_pos.mpr hT
  have hLpos : 0≤ L M := (le_max_left ..).trans h₁
  have hL2 : 8*log 2≤ L M := (le_max_right ..).trans h₁
  have hfloor : (T:ℝ)≤ u M := Nat.floor_le (exp_pos _).le
  have htwo : u M≤ 2*(T:ℝ) := by
    have ha : u M<(T:ℝ)+1 := Nat.lt_floor_add_one _
    have hh : (1:ℝ)≤ T := by exact_mod_cast hT
    linarith
  have hm : modulus T≤ M := by
    have hT3 := pow_le_pow_left₀ hpos.le hfloor 3
    have henv : (u M)^3 ≤ log M := by
      rw [show (u M)^3=exp (3*((1/4)*L M)) by exact (Real.exp_nat_mul ((1/4)*L M) 3).symm]
      rw [←Real.exp_log (by exact h₂ : 0< log M)]
      apply Real.exp_le_exp.mpr
      change 3*(1/4*L M)≤ L M; linarith
    have hlog := (ThetaLargeLawTails.modulus_log hT).trans (hT3.trans henv)
    have hm' : 0<(modulus T:ℝ) := by exact_mod_cast (pow_pos (Nat.factorial_pos T) T)
    have hM : 0<(M:ℝ) := lt_of_lt_of_le (by exact h₂ : 0 < log M) (Real.log_le_self (Nat.cast_nonneg _))
    exact_mod_cast (Real.log_le_log_iff hm' hM).mp hlog
  have huT := Real.log_le_log (exp_pos _) htwo
  rw [Real.log_mul (by norm_num) hpos.ne'] at huT
  simp only [Real.log_exp] at huT
  exact ⟨T,hp,hm,by change L M/8≤ log T;linarith,hLpos⟩

/-- Every reduced class contains finer positive and negative extreme classes of
modulus at most M, for every sufficiently large M depending on the given class. -/
theorem lower (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0 < q)
    (hr : r < q) (hc : r.Coprime q) : ∀ᶠ M : ℕ in atTop,
      ∃ m : ℕ, ∃ h : NeZero m, letI := h; m≤ M ∧ q∣m ∧ ∃ n< m, ∃ s< m,
        n.Coprime m ∧ s.Coprime m ∧ n%q=r ∧ s%q=r ∧
        (log (log M))^2/(512*Real.pi^2)≤ predictor m n ∧
          predictor m s≤ -((log (log M))^2/(512*Real.pi^2)) := by
  filter_upwards [choose_parameter _ (ThetaCompatibleMeans.both hAP hq hr hc)] with M H
  obtain ⟨T,⟨hm,hqm,n,hn,s,hs,hnc,hsc,hnq,hsq,hp,hneg⟩,hM,ht,hl⟩ := H
  refine ⟨modulus T,⟨by omega⟩,hM,hqm,n,hn,s,hs,hnc,hsc,hnq,hsq,?_,?_⟩
  all_goals
    have hh := pow_le_pow_left₀ (by positivity : 0≤ log (log M)/8) ht 2
    have h : (log (log M))^2/(512*Real.pi^2)≤ (log T)^2/(8*Real.pi^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg Real.pi)]
  · exact h.trans hp
  · rw [neg_div] at hneg; exact hneg.trans (neg_le_neg h)

#print axioms upper
#print axioms lower
end
end Arxiv.«2501.03234».ThetaClassMeanBudget
