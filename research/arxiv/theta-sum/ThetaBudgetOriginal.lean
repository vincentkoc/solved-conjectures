import ThetaSharpPeriodBudget

/-! The optimal mean-square approximation rate at an arbitrary integer period budget. -/
namespace Arxiv.«2501.03234».ThetaPeriodBudget
open Finset Filter Topology ThetaNaturalPrimeMeans ThetaLevelCoefficients ThetaFiniteProjection
open ThetaProgressionProjection ThetaCharacterPrimeMeans ThetaPeriodMeans ThetaDiagonalConstant
open ThetaVarianceExhaustion Complex
noncomputable section

private theorem arbitrary_budget {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ M : ℕ in atTop,
      (∀ m : ℕ, [NeZero m] → m≤M →
        1/((1048576*128^2)*Real.log M*Real.log (Real.log M))≤V-energy m) ∧
      ∃ m : ℕ, ∃ _ : NeZero m, m≤M ∧ V-energy m≤C/(Real.log M*Real.log (Real.log M)) := by
  obtain ⟨C,hC,H⟩ := period_budget hV hAP
  obtain ⟨K,hK⟩ := eventually_atTop.mp H
  let c : ℝ := 1048576*128^2
  have hc : 0<c := by dsimp [c]; norm_num
  refine ⟨24*C,by positivity,?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hlog.eventually_ge_atTop (6*K+144),eventually_ge_atTop 2] with M hM hM'
  let u := Real.log M
  change 6*(K:ℝ)+144≤u at hM
  have hu : 144≤u := by linarith [Nat.cast_nonneg (α:=ℝ) K]
  have hup : 0<u := by linarith
  let Y := ⌊u/6⌋₊
  have hfloor : (Y:ℝ)≤u/6 := Nat.floor_le (by positivity)
  have hnext : u/6<(Y:ℝ)+1 := Nat.lt_floor_add_one _
  have hY : K≤Y := (Nat.le_floor_iff (by positivity)).mpr (by linarith)
  have hY' : (12:ℝ)≤Y := by linarith
  have hyp : 0<(Y:ℝ) := by linarith
  have hl := Real.log_pos (show (1:ℝ)<Y by linarith)
  have hl' := Real.log_pos (show 1<u by linarith)
  have hratio : u≤12*Y := by linarith
  have hlogu : Real.log u≤2*Real.log Y := by
    have H₁ := Real.log_le_log hup hratio
    rw [Real.log_mul (by norm_num) hyp.ne'] at H₁
    linarith only [H₁,Real.log_le_log (by norm_num : (0:ℝ)<12) hY']
  have hupper := (hK Y hY).2
  constructor
  · intro m _ hm
    have hmm : Real.log m≤6*(Y+1:ℕ) := by
      have hh := Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos m)) (show (m:ℝ)≤M by exact_mod_cast hm)
      change Real.log m≤u at hh; push_cast; linarith
    have H := (hK (Y+1) (by omega)).1 m hmm
    apply le_trans _ H
    change 1/(c*u*Real.log u)≤1/(c*(Y+1:ℕ)*Real.log (Y+1:ℕ))
    have hz : (1:ℝ)<((Y+1:ℕ):ℝ) := by push_cast; linarith
    have hz' : ((Y+1:ℕ):ℝ)≤u := by push_cast; linarith
    apply one_div_le_one_div_of_le (mul_pos (mul_pos hc (by linarith)) (Real.log_pos hz))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hz' hc.le) (Real.log_le_log (by linarith) hz')
      (Real.log_pos hz).le (mul_nonneg hc.le hup.le)
  · refine ⟨Nat.lcmUpto Y,inferInstance,?_,hupper.2.trans ?_⟩
    · have hle : Real.log (Nat.lcmUpto Y)≤u := by linarith only [hupper.1,hfloor]
      exact_mod_cast (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.lcmUpto_pos Y)) (by exact_mod_cast (show 0<M by omega))).mp hle
    · change C/((Y:ℝ)*Real.log Y)≤24*C/(u*Real.log u)
      rw [div_le_div_iff₀ (mul_pos hyp hl) (mul_pos hup hl')]
      have hh := mul_le_mul hratio hlogu hl'.le (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_left hh hC.le]

private lemma periodic_limit {m : ℕ} [NeZero m] {g : ℕ → ℝ} (hg : OnMod m g) {V : ℝ}
    (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V)) (hAP : ProgressionMangoldt) :
    ∃ L : ℝ, V-energy m≤L ∧ Tendsto (primeMean (fun p => (residual p-g p)^2)) atTop (𝓝 L) := by
  let f (n : ℕ) := g n-diagonalConstant
  have hf : OnMod m f := fun n => by dsimp [f]; rw [hg n]
  let b := transform m f
  let L := V-energy m+∑ χ,‖value χ-b χ‖^2
  refine ⟨L,le_add_of_nonneg_right (sum_nonneg fun _ _ => sq_nonneg _),?_⟩
  have hlim := squared_error b hV hAP
  apply primeMean_of_close _ hlim
  intro e he
  filter_upwards [eventually_gt_atTop m] with p hp hprim
  have hc := hprim.coprime_iff_not_dvd.mpr (fun hh => hp.not_ge (Nat.le_of_dvd (NeZero.pos m) hh))
  simp only [b,inversion hf hc,←ofReal_sub,norm_real,Real.norm_eq_abs,sq_abs]
  have hz : centered p-f p=residual p-g p := by dsimp [centered,f]; ring
  rw [hz,sub_self,abs_zero]; exact he

/-- Sharp optimization over all real periodic predictors with period at most M.
The model is fixed before the prime endpoint tends to infinity. -/
theorem optimal_model_rate (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ M : ℕ in atTop,
      (∀ m : ℕ, 0 < m → m≤M → ∀ g : ℕ → ℝ, OnMod m g → ∃ L : ℝ,
        Tendsto (primeMean (fun p => (((S p:ℝ)/p-Real.log p/2)-g p)^2)) atTop (𝓝 L) ∧
        1/((1048576*128^2)*Real.log M*Real.log (Real.log M))≤L) ∧
      ∃ m : ℕ, 0 < m ∧ m≤M ∧ ∃ g : ℕ → ℝ, OnMod m g ∧ ∃ L : ℝ,
        Tendsto (primeMean (fun p => (((S p:ℝ)/p-Real.log p/2)-g p)^2)) atTop (𝓝 L) ∧
        L≤C/(Real.log M*Real.log (Real.log M)) := by
  obtain ⟨_,V,_,_,_,_,hV,_⟩ := S_prime_class_statistics hAP
  obtain ⟨C,hC,H⟩ := arbitrary_budget hV hAP
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with M hM
  constructor
  · intro m hm hmM g hg
    let : NeZero m := ⟨hm.ne'⟩
    obtain ⟨L,hlo,hlim⟩ := periodic_limit hg hV hAP
    exact ⟨L,hlim,(hM.1 m hmM).trans hlo⟩
  · obtain ⟨m,hm,hmM,hb⟩ := hM.2
    let g (p : ℕ) := diagonalConstant+predictor m p
    have hg : OnMod m g := fun n => by dsimp [g]; rw [predictor_periodic m n]
    refine ⟨m,NeZero.pos m,hmM,g,hg,V-energy m,?_,hb⟩
    have hlim := optimal_error m hV hAP
    apply hlim.congr; intro p
    unfold primeMean; congr 1; apply sum_congr rfl; intro q _
    change (residual q-diagonalConstant-predictor m q)^2=(residual q-(diagonalConstant+predictor m q))^2
    ring

end
end Arxiv.«2501.03234».ThetaPeriodBudget
#print axioms Arxiv.«2501.03234».ThetaPeriodBudget.optimal_model_rate
