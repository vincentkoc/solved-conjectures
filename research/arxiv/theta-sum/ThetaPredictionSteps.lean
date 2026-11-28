import ThetaUniformPrimePrediction

/-! Limits of the conditional finite models and the size of one extra
prime-power-coordinate step for the original arithmetic predictors. -/
namespace Arxiv.«2501.03234».ThetaPredictionSteps
open Filter Real Finset ThetaClassConcentration ThetaUniformPrimePrediction ThetaConditionalApproximation
open ThetaSmoothConditionalModel ThetaExposureLayers ThetaUnitExposure ThetaConditionalRows ThetaIdentityFiber
open ThetaDyadicLaw ThetaNaturalPrimeMeans ThetaPrimeLaw ThetaCharacterPrimeMeans ThetaDiagonalConstant
open ThetaPeriodMeans ThetaPrimeTailTransfer ThetaProgressionProjection
open scoped Topology
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
local instance (T : ℕ) : NeZero (m T) := ⟨(ThetaCompactModulus.positive T).ne'⟩

theorem divides {T U : ℕ} (h : T≤U) : m T∣m U := by
  apply pow_dvd_pow_of_dvd _ 4
  exact lcm_dvd (fun i hi => dvd_lcm ((Icc_subset_Icc (le_refl 1) h) hi))

def modelMean (T r Y V : ℕ) := diagonalConstant+(8/π^2)*cond (m T) r Y (standardWindow V)

theorem calibrated (hAP : ProgressionMangoldt) {T r : ℕ} (hr : r< m T) (hc : r.Coprime (m T))
    {ε : ℝ} (he : 0<ε) : ∀ᶠ Y : ℕ in atTop, ∀ᶠ V : ℕ in atTop,
    |prediction T r-modelMean T r Y V|≤ε := by
  let M := m T
  have hm : 0< M := ThetaCompactModulus.positive T
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  let δ := ε/(8*(M.totient:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [eventually_ge_atTop M,residual_models_approximate hδ] with Y hY hmod
  filter_upwards [hmod] with V H
  let g := residualModel Y V
  have hd := Nat.dvd_factorial hm hY
  have hu := (unitMean_lift hd (selectClass_mod r M)).trans (unit_class hr hc)
  have hc₀ := periodic hAP hm hd hr hc (residualModel_periodic Y V)
  have hmean : (M.totient:ℝ)*unitMean Y.factorial (fun n => selectClass r M n*g n)=modelMean T r Y V := by
    let w (n : ℕ) := selectClass r M n
    let f (n : ℕ) := w n*model Y V n
    have eqn : (fun n => selectClass r M n*g n)=(fun n => diagonalConstant*w n+(8/π^2)*f n) :=
      funext (fun n => by dsimp [g,f,w,residualModel]; ring)
    change (M.totient:ℝ)*unitMean Y.factorial _=diagonalConstant+(8/π^2)*((M.totient:ℝ)*unitMean Y.factorial f)
    rw [eqn]; unfold unitMean at hu ⊢
    rw [sum_add_distrib,←mul_sum,←mul_sum]
    change (∑ x : (ZMod Y.factorial)ˣ,w (x:ZMod Y.factorial).val)/(Y.factorial.totient:ℝ)=1/(M.totient:ℝ) at hu
    calc _ = diagonalConstant*((M.totient:ℝ)*((∑ x : (ZMod Y.factorial)ˣ,w (x:ZMod Y.factorial).val)/Y.factorial.totient))+
                   (8/π^2)*((M.totient:ℝ)*((∑ x : (ZMod Y.factorial)ˣ,f (x:ZMod Y.factorial).val)/Y.factorial.totient)) := by ring
         _ = _ := by rw [hu]; field_simp
  change Tendsto (progressionMean M r g) atTop (𝓝 _) at hc₀
  rw [hmean] at hc₀
  have hf := Metric.tendsto_nhds.mp (original_mean M r hc hr hAP) (ε/4) (by positivity)
  have hg := Metric.tendsto_nhds.mp hc₀ (ε/4) (by positivity)
  have herr := restrict_error hAP hm hr hc (fun n => abs_nonneg (residual n-g n)) H
  obtain ⟨X,hf,hg,her⟩ := (hf.and (hg.and herr)).exists
  rw [Real.dist_eq] at hf hg
  change |progressionMean M r residual X-prediction T r|<_ at hf
  have hcmp : |progressionMean M r residual X-progressionMean M r g X|≤
    progressionMean M r (fun n => |residual n-g n|) X := by
    unfold progressionMean
    rw [←sub_div,←sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (ThetaPrimeDensity.primeSet (fun n => n%M=r) X).card : (0:ℝ)≤_)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs ..) (Nat.cast_nonneg _)
  have hscale : 2*(M.totient:ℝ)*δ=ε/4 := by dsimp [δ];field_simp;ring
  rw [hscale] at her
  have h₁ := abs_sub_le (prediction T r) (progressionMean M r residual X) (modelMean T r Y V)
  have h₂ := abs_sub_le (progressionMean M r residual X) (progressionMean M r g X) (modelMean T r Y V)
  rw [abs_sub_comm (prediction T r) (progressionMean M r residual X)] at h₁
  linarith only [h₁,h₂,hf,hg,hcmp,her,he]

def incrementCost (T : ℕ) := 544*envelope*(log (T+1:ℕ))^2/(T+1:ℕ)
def stepCost (T : ℕ) := (8/π^2)*(bias (T+1)+incrementCost T+bias T)

theorem cost_zero : Tendsto stepCost atTop (𝓝 0) := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have H (a : ℝ) (ha : 0<a) : Tendsto (fun t : ℕ => (log (t:ℝ))^2/(t:ℝ)^a) atTop (𝓝 0) := by
    simpa only [Function.comp_def,rpow_two] using (isLittleO_log_rpow_rpow_atTop 2 ha).tendsto_div_nhds_zero.comp hn
  have hb : Tendsto bias atTop (𝓝 0) := by
    have h := (H _ (by norm_num : (0:ℝ)<1/16)).const_mul ((2160*ThetaIdentityModels.Z)*(612*ThetaFactorialRows.zetaBound))
    rw [mul_zero] at h; exact h.congr (fun x => by dsimp [bias];ring)
  have hi : Tendsto incrementCost atTop (𝓝 0) := by
    have h := ((H _ zero_lt_one).const_mul (544*envelope)).comp (tendsto_add_atTop_nat 1)
    rw [mul_zero] at h; exact h.congr (fun x => by dsimp [incrementCost];rw [rpow_one];ring)
  have h := (((hb.comp (tendsto_add_atTop_nat 1)).add hi).add hb).const_mul (8/π^2)
  simp only [add_zero,mul_zero] at h; exact h

theorem finite_step {T Y V r : ℕ} (hr : r< m (T+1)) (hc : r.Coprime (m (T+1)))
    (hP : m (T+1)∣Y.factorial) (hT : 2≤T) (hl : 1≤log T) :
    |modelMean (T+1) r Y V-modelMean T (r%m T) Y V|≤ stepCost T := by
  let P := Y.factorial
  let M := m (T+1)
  let V' := standardWindow V
  have hd : m T∣M := divides (Nat.le_succ T)
  obtain ⟨x,hx⟩ := ZMod.unitsMap_surjective hP (ZMod.unitOfCoprime r hc)
  have hcast : ((x:ZMod P).val:ZMod M)=(r:ZMod M) := by
    have h := congrArg (fun u : (ZMod M)ˣ => (u:ZMod M)) hx
    rw [ZMod.unitsMap_val,ZMod.coe_unitOfCoprime,← ZMod.natCast_zmod_val (x:ZMod P),ZMod.cast_natCast hP] at h
    exact h
  have hkey : key M x=r := by
    change (x:ZMod P).val%M=r
    exact ((ZMod.natCast_eq_natCast_iff' ..).mp hcast).trans (Nat.mod_eq_of_lt hr)
  have hkey' : key (m T) x = r%m T := by rw [←hkey];exact (Nat.mod_mod_of_dvd _ hd).symm
  have hl' := hl.trans (log_le_log (by exact_mod_cast (show 0<T by omega) : 0<(T:ℝ))
    (Nat.cast_le.mpr (Nat.le_succ T)))
  have h₁ := approximation (show 2≤T+1 by omega) hl' hP V' x
  have h₂ := approximation hT hl (hd.trans hP) V' x
  change |value Y V' (T+1) x-cond M (key M x) Y V'|≤_ at h₁
  rw [hkey,abs_sub_comm] at h₁; rw [hkey'] at h₂
  have hstep : |value Y V' (T+1) x-value Y V' T x|≤ incrementCost T :=
    ThetaFiniteExposure.increment _ _ _ (ThetaUnitExposure.refine (ThetaCenteredExposure.modulus_dvd (Nat.le_succ T)))
      (fun u v he => oscillation hl' V' u v he) x
  have hdiff := abs_sub_le (cond M r Y V') (value Y V' (T+1) x) (cond (m T) (r%m T) Y V')
  have hdiff' := abs_sub_le (value Y V' (T+1) x) (value Y V' T x) (cond (m T) (r%m T) Y V')
  have ha : |cond M r Y V'-cond (m T) (r%m T) Y V'|≤bias (T+1)+incrementCost T+bias T := by
    linarith only [hdiff,hdiff',h₁,h₂,hstep]
  have heq : modelMean (T+1) r Y V-modelMean T (r%m T) Y V=(8/π^2)*(cond M r Y V'-cond (m T) (r%m T) Y V') := by dsimp [modelMean,M,V'];ring
  rw [heq,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤8/π^2)]
  exact mul_le_mul_of_nonneg_left ha (by positivity)

theorem small_jumps (hAP : ProgressionMangoldt) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ T : ℕ in atTop, ∀ r< m (T+1), r.Coprime (m (T+1)) →
      |prediction (T+1) r-prediction T (r%m T)|≤ε := by
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),hl.eventually_ge_atTop 1,cost_zero.eventually_le_const (show 0<ε/4 by positivity)] with T ht hlog hcost
  intro r hr hc
  have hm := ThetaCompactModulus.positive T
  have hd := divides (Nat.le_succ T)
  have hu : (r%m T).Coprime (m T) := by change Nat.gcd (r%m T) (m T)=1;rw [←Nat.gcd_rec];exact (hc.coprime_dvd_right hd).symm
  have h₁ := calibrated hAP hr hc (show 0<ε/4 by positivity)
  have h₂ := calibrated hAP (Nat.mod_lt r hm) hu (show 0<ε/4 by positivity)
  obtain ⟨Y,hy,hY,hY'⟩ := ((eventually_ge_atTop (m (T+1))).and (h₁.and h₂)).exists
  obtain ⟨V,hV,hV'⟩ := (hY.and hY').exists
  have h₃ := finite_step (V:=V) hr hc (Nat.dvd_factorial (ThetaCompactModulus.positive _) hy) ht hlog
  have h₄ := abs_sub_le (prediction (T+1) r) (modelMean (T+1) r Y V) (prediction T (r%m T))
  have h₅ := abs_sub_le (modelMean (T+1) r Y V) (modelMean T (r%m T) Y V) (prediction T (r%m T))
  rw [abs_sub_comm (prediction T (r%m T))] at hV'
  linarith only [h₄,h₅,h₃,hcost,hV,hV',he]

#print axioms finite_step
#print axioms cost_zero
#print axioms small_jumps

#print axioms divides
#print axioms calibrated
end
end Arxiv.«2501.03234».ThetaPredictionSteps
