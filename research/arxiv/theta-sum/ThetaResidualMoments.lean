import ThetaSievedConcentration
import ThetaDyadicLaw
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exponential square-root integrability and prime moments of the signed residual. -/
namespace Arxiv.«2501.03234».ThetaResidualMoments
open MeasureTheory Set Filter Finset
open scoped Topology
noncomputable section

private def Tail (μ : ProbabilityMeasure ℝ) (C a : ℝ) : Prop :=
  ∀ t : ℝ, 0≤t → (μ:Measure ℝ).real {x : ℝ | t< |x|} ≤ C*Real.exp (-a*Real.sqrt t)

/-- An exponential tail for a nonnegative test bounds its exponential moment. -/
theorem exp_moment_of_tail {μ : ProbabilityMeasure ℝ} {C : ℝ} (hC : 0≤C)
    {U : ℝ → ℝ} (hU : Continuous U) (hpos : ∀ x, 0≤U x)
    (htail : ∀ {t : ℝ}, 0≤t → (μ:Measure ℝ) {x : ℝ | t < U x}≤ENNReal.ofReal (C*Real.exp (-2*t))) :
    Integrable (fun x => Real.exp (U x)) (μ:Measure ℝ) ∧
      (∫ x, Real.exp (U x) ∂(μ:Measure ℝ))≤1+C := by
  let G (x : ℝ) := Real.exp (U x)-1
  have hG : Continuous G := hU.rexp.sub continuous_const
  have hGpos (x) : 0≤G x := sub_nonneg.mpr (Real.one_le_exp (hpos x))
  have hc := lintegral_comp_eq_lintegral_meas_lt_mul (μ:Measure ℝ)
    (Eventually.of_forall hpos) hU.aemeasurable
    (g:=Real.exp) (fun t _ => Real.continuous_exp.intervalIntegrable ..)
    (Eventually.of_forall Real.exp_nonneg)
  simp only [integral_exp,Real.exp_zero] at hc
  have hlin : (∫⁻ x, ENNReal.ofReal (G x) ∂(μ:Measure ℝ))≤ENNReal.ofReal C := by
    change (∫⁻ x, ENNReal.ofReal (Real.exp (U x)-1) ∂(μ:Measure ℝ))≤_
    rw [hc]
    calc
      _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (C*Real.exp (-t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
        refine le_trans (b:=ENNReal.ofReal (C*Real.exp (-2*t))*ENNReal.ofReal (Real.exp t)) ?_ (le_of_eq ?_)
        · gcongr; exact htail (le_of_lt ht)
        rw [←ENNReal.ofReal_mul (mul_nonneg hC (Real.exp_nonneg _)),mul_assoc,←Real.exp_add]
        congr 3; ring
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_neg_Ioi 0).const_mul C)
          (Eventually.of_forall (fun t => mul_nonneg hC (Real.exp_nonneg _))),
          integral_const_mul,integral_exp_neg_Ioi_zero,mul_one]
  have hi : Integrable G (μ:Measure ℝ) := (lintegral_ofReal_ne_top_iff_integrable hG.aestronglyMeasurable
    (Eventually.of_forall hGpos)).mp (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top).ne
  have he : (fun x => Real.exp (U x))=(fun x => G x+1) := by funext x; simp [G]
  change Integrable (fun x => Real.exp (U x)) _ ∧ _≤_
  rw [he]
  refine ⟨hi.add (integrable_const _),?_⟩
  rw [integral_add hi (integrable_const _),integral_const]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hGpos)] at hlin
  have := (ENNReal.ofReal_le_ofReal_iff hC).mp hlin
  simpa [add_comm] using add_le_add_right this 1

/-- Layer cake at half the tail exponent bounds the exponential moment by 1+C. -/
private theorem exponential_moment {μ : ProbabilityMeasure ℝ} {C a : ℝ} (hC : 0≤C) (ha : 0<a)
    (h : Tail μ C a) :
    Integrable (fun x : ℝ => Real.exp ((a/2)*Real.sqrt |x|)) (μ:Measure ℝ) ∧
    (∫ x : ℝ, Real.exp ((a/2)*Real.sqrt |x|) ∂(μ:Measure ℝ))≤1+C := by
  let U (x : ℝ) := (a/2)*Real.sqrt |x|
  have hU : Continuous U := by dsimp [U]; fun_prop
  have hpos (x) : 0≤U x := by dsimp [U]; positivity
  have htail {t : ℝ} (ht : 0≤t) :
      (μ:Measure ℝ) {x : ℝ | t<U x}≤ENNReal.ofReal (C*Real.exp (-2*t)) := by
    let v := 2*t/a
    have hv : 0≤v := by dsimp [v]; positivity
    have he (x : ℝ) : t<U x ↔ v^2< |x| := by
      have h₁ : t<U x ↔ v<Real.sqrt |x| := by
        dsimp [v,U]; rw [div_lt_iff₀ ha]; constructor <;> intro H <;> linarith
      rw [h₁]; constructor
      · intro hs; nlinarith only [sq_lt_sq' (show -Real.sqrt |x|<v by linarith) hs,Real.sq_sqrt (abs_nonneg x)]
      · intro hs; by_contra! hn
        nlinarith only [hs,pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2,Real.sq_sqrt (abs_nonneg x)]
    rw [show {x : ℝ | t<U x}={x : ℝ | v^2< |x|} from Set.ext he,← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have H := h (v^2) (sq_nonneg _)
    rw [Real.sqrt_sq hv] at H
    have hav : -a*v= -2*t := by dsimp [v]; field_simp
    rwa [hav] at H
  exact exp_moment_of_tail hC hU hpos htail

private lemma power_bound (b : ℝ) (hb : 0<b) (k : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ x : ℝ, |x|^k≤D*Real.exp (b*Real.sqrt |x|) := by
  let n := 2*k
  let D : ℝ := n.factorial/b^n
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro x
  have he := Real.pow_div_factorial_le_exp _ (mul_nonneg hb.le (Real.sqrt_nonneg |x|)) n
  have hf : 0<(n.factorial:ℝ) := by positivity
  have hs : (Real.sqrt |x|)^n=|x|^k := by rw [show n=2*k from rfl,pow_mul,Real.sq_sqrt (abs_nonneg _)]
  rw [mul_pow,hs,div_le_iff₀ hf] at he
  dsimp [D]; rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hb _)]
  linarith only [he]

private lemma moment_bound {C a : ℝ} (hC : 0≤C) (ha : 0<a) (k : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ μ : ProbabilityMeasure ℝ, Tail μ C a →
      Integrable (fun x : ℝ => |x|^k) (μ:Measure ℝ) ∧
      (∫ x : ℝ, |x|^k ∂(μ:Measure ℝ))≤D := by
  obtain ⟨K,hK,H⟩ := power_bound (a/2) (half_pos ha) k
  refine ⟨K*(1+C),by positivity,?_⟩
  intro μ hμ
  obtain ⟨hi,hv⟩ := exponential_moment hC ha hμ
  have hg : Integrable (fun x : ℝ => |x|^k) (μ:Measure ℝ) :=
    (hi.const_mul K).mono' (by fun_prop) (Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using H x))
  refine ⟨hg,(integral_mono hg (hi.const_mul K) H).trans ?_⟩
  rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hv hK

private lemma limit_tail {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {C a : ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) (h : ∀ᶠ n in atTop,Tail (ν n) C a) : Tail μ C a := by
  intro t ht
  let s := {x : ℝ | t< |x|}
  have hopen : IsOpen s := isOpen_lt continuous_const continuous_abs
  have hrow : ∀ᶠ n in atTop,(ν n:Measure ℝ) s≤ENNReal.ofReal (C*Real.exp (-a*Real.sqrt t)) := by
    filter_upwards [h] with n hn
    rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal (hn t ht)
  have H := (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hopen).trans
    (liminf_le_of_frequently_le' hrow.frequently)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top H).trans_eq
    (ENNReal.toReal_ofReal (by
      obtain ⟨n,hn⟩ := h.exists
      exact (measureReal_nonneg (μ:=((ν n):Measure ℝ)) (s:=s)).trans (hn t ht)))

private def clip (M y : ℝ) := max (-M) (min M y)
private lemma clip_abs {M : ℝ} (hM : 0≤M) (y : ℝ) : |clip M y|≤M :=
  abs_le.mpr ⟨le_max_left ..,max_le (by linarith) (min_le_left ..)⟩

private lemma clip_err {M : ℝ} (hM : 0<M) (y : ℝ) : |y-clip M y|≤y^2/M := by
  rw [le_div_iff₀ hM]
  by_cases hl : y< -M
  · have hy : y≤M := by linarith
    simp only [clip,min_eq_right hy,max_eq_left hl.le,sub_neg_eq_add,abs_of_nonpos (show y+M≤0 by linarith)]
    nlinarith only [mul_nonneg (by linarith : 0≤ -y-M) (by linarith : 0≤ -y),sq_nonneg M]
  by_cases hh : y≤M
  · simp [clip,min_eq_right hh,max_eq_right (le_of_not_gt hl),sq_nonneg]
  · simp only [clip,min_eq_left (le_of_not_ge hh),max_eq_right (by linarith : -M≤M),
      abs_of_nonneg (by linarith : 0≤y-M)]
    nlinarith only [sq_nonneg (y-M),mul_nonneg hM.le (by linarith : 0≤y-M)]

private lemma test_moments {C a K : ℝ} (hC : 0≤C) (ha : 0<a) {k : ℕ} {φ : ℝ → ℝ}
    (hc : Continuous φ) (hg : ∀ x, |φ x|≤K*(1+|x|^k)) :
    ∃ D : ℝ, 0≤D ∧ ∀ μ : ProbabilityMeasure ℝ, Tail μ C a →
      Integrable φ (μ:Measure ℝ) ∧ Integrable (fun x => φ x^2) (μ:Measure ℝ) ∧
      (∫ x, φ x^2 ∂(μ:Measure ℝ))≤D := by
  obtain ⟨D,hD,H⟩ := moment_bound hC ha (k*2)
  obtain ⟨_,_,J⟩ := moment_bound hC ha k
  refine ⟨2*K^2*(1+D),by positivity,?_⟩
  intro μ hm
  obtain ⟨hi,hv⟩ := H μ hm
  have hf : Integrable φ (μ:Measure ℝ) := (((integrable_const 1).add (J μ hm).1).const_mul K).mono'
    hc.aestronglyMeasurable (Eventually.of_forall (fun x => hg x))
  let g (x : ℝ) := 2*K^2*(1+|x|^(k*2))
  have hgi : Integrable g (μ:Measure ℝ) := ((integrable_const 1).add hi).const_mul _
  have hg' (x) : φ x^2≤g x := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) (hg x) 2
    rw [sq_abs] at hsq; dsimp [g]; rw [pow_mul]
    nlinarith only [hsq,mul_nonneg (sq_nonneg K) (sq_nonneg (1-|x|^k))]
  have hi' : Integrable (fun x => φ x^2) (μ:Measure ℝ) := hgi.mono' (by fun_prop)
    (Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hg' x))
  refine ⟨hf,hi',(integral_mono hi' hgi hg').trans ?_⟩
  dsimp [g]; rw [integral_const_mul,integral_add (integrable_const _) hi,integral_const]
  simpa using mul_le_mul_of_nonneg_left (add_le_add_right hv 1) (show 0≤2*K^2 by positivity)

private lemma clip_integral {μ : ProbabilityMeasure ℝ} {φ : ℝ → ℝ} (hc : Continuous φ)
    (hi : Integrable φ (μ:Measure ℝ)) (hsq : Integrable (fun x => φ x^2) (μ:Measure ℝ))
    {D M : ℝ} (hv : (∫ x, φ x^2 ∂(μ:Measure ℝ))≤D) (hM : 0<M) :
    |(∫ x, φ x ∂(μ:Measure ℝ))-(∫ x, clip M (φ x) ∂(μ:Measure ℝ))|≤D/M := by
  have hclip : Integrable (fun x => clip M (φ x)) (μ:Measure ℝ) := (integrable_const M).mono'
    (by unfold clip; fun_prop) (Eventually.of_forall (fun x => clip_abs hM.le _))
  rw [←integral_sub hi hclip,←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono (hi.sub hclip).norm (hsq.div_const M)
    (fun x => clip_err hM (φ x))).trans
  rw [integral_div]; exact div_le_div_of_nonneg_right hv hM.le

private lemma tests_of_tail {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {C a : ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) (h : ∀ᶠ n in atTop,Tail (ν n) C a) (hC : 0≤C) (ha : 0<a)
    {φ : ℝ → ℝ} (hc : Continuous φ) {K : ℝ} {k : ℕ} (hg : ∀ x, |φ x|≤K*(1+|x|^k)) :
    Integrable φ (μ:Measure ℝ) ∧
    Tendsto (fun n => ∫ x, φ x ∂(ν n:Measure ℝ)) atTop (𝓝 (∫ x, φ x ∂(μ:Measure ℝ))) := by
  obtain ⟨D,hD,H⟩ := test_moments hC ha hc hg
  obtain ⟨hi,hs,hb⟩ := H μ (limit_tail hν h)
  refine ⟨hi,Metric.tendsto_nhds.mpr ?_⟩
  intro ε he
  let M := 1+4*D/ε
  have hM : 0<M := by dsimp [M]; positivity
  have hsmall : D/M<ε/4 := by rw [div_lt_iff₀ hM]; dsimp [M]; field_simp; linarith
  let f : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => clip M (φ x), by unfold clip; fun_prop⟩ (2*M) (fun x y => by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by simpa [two_mul] using add_le_add (clip_abs hM.le (φ x)) (clip_abs hM.le (φ y))))
  have hf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν f
  filter_upwards [h,Metric.tendsto_nhds.mp hf (ε/2) (half_pos he)] with n hrow hn
  obtain ⟨hi',hs',hb'⟩ := H _ hrow
  have h₁ := clip_integral hc hi' hs' hb' hM
  have h₂ := clip_integral hc hi hs hb hM
  change dist (∫ x, clip M (φ x) ∂(ν n:Measure ℝ)) (∫ x, clip M (φ x) ∂(μ:Measure ℝ))< _ at hn
  rw [Real.dist_eq] at hn ⊢
  simpa only using calc
    |(∫ x, φ x ∂(ν n:Measure ℝ))-(∫ x, φ x ∂(μ:Measure ℝ))| ≤
        |(∫ x, φ x ∂(ν n:Measure ℝ))-(∫ x, clip M (φ x) ∂(ν n:Measure ℝ))|+
        |(∫ x, clip M (φ x) ∂(ν n:Measure ℝ))-(∫ x, clip M (φ x) ∂(μ:Measure ℝ))|+
        |(∫ x, φ x ∂(μ:Measure ℝ))-(∫ x, clip M (φ x) ∂(μ:Measure ℝ))| := by
      rw [abs_sub_comm (∫ x, φ x ∂(μ:Measure ℝ))]
      linarith only [abs_sub_le (∫ x, φ x ∂(ν n:Measure ℝ)) (∫ x, clip M (φ x) ∂(ν n:Measure ℝ)) (∫ x, clip M (φ x) ∂(μ:Measure ℝ)),
        abs_sub_le (∫ x, φ x ∂(ν n:Measure ℝ)) (∫ x, clip M (φ x) ∂(μ:Measure ℝ)) (∫ x, φ x ∂(μ:Measure ℝ))]
    _ < ε := by linarith only [h₁,h₂,hn,hsmall]

open ThetaCharacterPrimeMeans ThetaPrimeLaw ThetaNaturalPrimeMeans ThetaProfiniteUnits ThetaPrimeDensity
private lemma empirical_tail_of_count {C a : ℝ} (H : ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0≤t →
    ((primeSet (fun p => t≤|residual p|) X).card:ℝ)≤C*Nat.primeCounting X*Real.exp (-a*Real.sqrt t)) :
    ∀ X : ℕ, 2≤X → Tail (empirical residual X) C a := by
  intro X hX t ht
  have hs : IsOpen {x : ℝ | t< |x|} := isOpen_lt continuous_const continuous_abs
  rw [empirical_real_set hX residual hs.measurableSet]
  have hπ : (0:ℝ)<Nat.primeCounting X := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hh => (Nat.primeCounting_eq_zero_iff.mp hh).not_gt hX)
  apply (div_le_iff₀ hπ).mpr
  have hc : primeSet (fun p => residual p∈{x : ℝ | t< |x|}) X ⊆
      primeSet (fun p => t≤|(S p:ℝ)/p-Real.log p/2|) X := by
    intro p hp; obtain ⟨hm,hs⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hm,le_of_lt hs⟩
  have hcount : ((primeSet (fun p => t< |residual p|) X).card:ℝ)≤(primeSet (fun p => t≤|residual p|) X).card := Nat.cast_le.mpr (Finset.card_le_card hc)
  have hc' := hcount.trans (H X hX t ht)
  exact hc'.trans_eq (by ring)

private theorem empirical_tail : ∃ C a : ℝ, 0<C ∧ 0<a ∧ ∀ X : ℕ, 2≤X → Tail (empirical residual X) C a := by
  obtain ⟨C,a,hC,ha,H⟩ := ThetaSievedConcentration.prime_normalized_tail
  exact ⟨C,a,hC,ha,empirical_tail_of_count H⟩

/-- The same constants bound the open tail of the limiting law and the closed empirical tails. -/
theorem prime_and_limit_tails (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    ∃ C a : ℝ, 0<C ∧ 0<a ∧
      (∀ t : ℝ, 0≤t → (haarLaw F:Measure ℝ).real {x : ℝ | t< |x|}≤C*Real.exp (-a*Real.sqrt t)) ∧
      ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0≤t → ((primeSet (fun p => t≤|residual p|) X).card:ℝ)≤
        C*Nat.primeCounting X*Real.exp (-a*Real.sqrt t) := by
  obtain ⟨C,a,hC,ha,H⟩ := ThetaSievedConcentration.prime_normalized_tail
  refine ⟨C,a,hC,ha,limit_tail (empirical_tendsto hAP hF) ?_,H⟩
  exact (eventually_ge_atTop 2).mono (empirical_tail_of_count H)

/-- The limit law and every prime sample share an exponential square-root moment. -/
theorem exponential_square_root (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    ∃ b D : ℝ, 0<b ∧ 0<D ∧
      (Integrable (fun x : ℝ => Real.exp (b*Real.sqrt |x|)) (haarLaw F:Measure ℝ) ∧
       (∫ x : ℝ, Real.exp (b*Real.sqrt |x|) ∂(haarLaw F:Measure ℝ))≤D) ∧
      ∀ X : ℕ, 2≤X → primeMean (fun p => Real.exp (b*Real.sqrt |residual p|)) X ≤ D := by
  obtain ⟨C,a,hC,ha,H⟩ := empirical_tail
  refine ⟨a/2,1+C,half_pos ha,by positivity,exponential_moment hC.le ha
    (limit_tail (empirical_tendsto hAP hF) ((eventually_ge_atTop 2).mono H)),?_⟩
  intro X hX
  have hb := (exponential_moment hC.le ha (H X hX)).2
  rwa [empirical_integral hX residual (by fun_prop)] at hb

/-- Weak convergence extends to every continuous test of at most polynomial growth. -/
theorem prime_polynomial_growth (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {φ : ℝ → ℝ} (hc : Continuous φ) {K : ℝ} {k : ℕ} (hg : ∀ x, |φ x|≤K*(1+|x|^k)) :
    Integrable φ (haarLaw F:Measure ℝ) ∧ Tendsto (primeMean (fun p => φ (residual p))) atTop
      (𝓝 (∫ x, φ x ∂(haarLaw F:Measure ℝ))) := by
  obtain ⟨C,a,hC,ha,H⟩ := empirical_tail
  obtain ⟨hi,hlim⟩ := tests_of_tail (empirical_tendsto hAP hF) ((eventually_ge_atTop 2).mono H) hC.le ha hc hg
  exact ⟨hi,hlim.congr' ((eventually_ge_atTop 2).mono fun X hX => empirical_integral hX residual hc.measurable)⟩

open ThetaDyadicLaw
private theorem progression_tail (hAP : ProgressionMangoldt) {q r : ℕ}
    (hq : 0<q) (hr : r.Coprime q) (hlt : r<q) {C a : ℝ}
    (H : ∀ X : ℕ, 2≤X → Tail (empirical residual X) C a) :
    ∀ᶠ X in atTop,Tail (progressionLaw q r residual X) (2*q.totient*C) a := by
  classical
  let P := primeSet (fun p => p%q=r)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hfreq := (class_prime_density hAP hq hr hlt).eventually_const_lt
    (show 1/(2*(q.totient:ℝ))<1/(q.totient:ℝ) by rw [div_lt_div_iff₀ (by positivity) hφ]; linarith)
  filter_upwards [eventually_ge_atTop 2,hfreq,class_nonempty hAP hq hr hlt] with X hX hfreq hne
  intro t ht
  let s := {x : ℝ | t< |x|}
  have hm : MeasurableSet s := (isOpen_lt continuous_const continuous_abs).measurableSet
  have HI := H X hX t ht
  change (empirical residual X:Measure ℝ).real s≤_ at HI
  rw [empirical_real_set hX residual hm] at HI
  have hπ : (0:ℝ)<Nat.primeCounting X := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hh => (Nat.primeCounting_eq_zero_iff.mp hh).not_gt hX)
  have hP : 0<((P X).card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hcard : ((P X).filter (fun p => residual p∈s)).card≤(primeSet (fun p => residual p∈s) X).card := by
    apply Finset.card_le_card
    intro p hp; obtain ⟨hQ,he⟩ := mem_filter.mp hp
    have hQ' : p∈Nat.primesLE X ∧ p%q=r := by simpa only [P,primeSet,mem_filter] using hQ
    exact mem_filter.mpr ⟨hQ'.1,he⟩
  have heq : (progressionLaw q r residual X:Measure ℝ).real s =
      ((P X).filter (fun p => residual p∈s)).card/((P X).card:ℝ) := by
    rw [←integral_indicator_one hm,progression_integral hne residual (measurable_one.indicator hm)]
    simp only [progressionMean,Set.indicator_apply,Pi.one_apply,sum_boole]; rfl
  change (progressionLaw q r residual X:Measure ℝ).real s≤_
  rw [heq,div_le_iff₀ hP]
  change 1/(2*(q.totient:ℝ))<((P X).card:ℝ)/Nat.primeCounting X at hfreq
  rw [div_lt_div_iff₀ (by positivity) hπ,one_mul] at hfreq
  have hbound := (div_le_iff₀ hπ).mp HI
  have hpos : 0≤C*Real.exp (-a*Real.sqrt t) := (measureReal_nonneg (μ:=((empirical residual X):Measure ℝ)) (s:=s)).trans (H X hX t ht)
  apply (Nat.cast_le.mpr hcard).trans (hbound.trans ?_)
  nlinarith only [mul_le_mul_of_nonneg_left hfreq.le hpos]

/-- Every reduced dyadic class has the same limits for polynomial-growth tests,
using the count of primes in the class as its denominator. -/
theorem dyadic_polynomial_growth (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {l r : ℕ} (hr : r.Coprime (2^l)) (hlt : r<2^l)
    {φ : ℝ → ℝ} (hc : Continuous φ) {K : ℝ} {k : ℕ} (hg : ∀ x, |φ x|≤K*(1+|x|^k)) :
    Tendsto (progressionMean (2^l) r (fun p => φ (residual p))) atTop
      (𝓝 (∫ x, φ x ∂(haarLaw F:Measure ℝ))) := by
  obtain ⟨C,a,hC,ha,H⟩ := empirical_tail
  obtain ⟨_,hlim⟩ := tests_of_tail (progression_law_tendsto hAP hr hlt hF)
    (progression_tail hAP (by positivity) hr hlt H) (by positivity) ha hc hg
  exact hlim.congr' ((class_nonempty hAP (by positivity) hr hlt).mono fun X hX =>
    progression_integral hX residual hc.measurable)

open ThetaDiagonalConstant
lemma centered_growth (B : ℝ) (k : ℕ) (x : ℝ) :
    |(x-B)^k|≤(1+|B|)^k*(1+|x|^k) := by
  rw [abs_pow]
  have h := abs_sub x B
  have hK : 0≤(1+|B|)^k := by positivity
  by_cases hx : |x|≤1
  · apply (pow_le_pow_left₀ (abs_nonneg _) (show |x-B|≤1+|B| by linarith only [h,hx]) k).trans
    exact le_mul_of_one_le_right hK (by have := pow_nonneg (abs_nonneg x) k; linarith)
  · have hg : |B|≤|B| * |x| := le_mul_of_one_le_right (abs_nonneg _) (le_of_not_ge hx)
    have hn := pow_le_pow_left₀ (abs_nonneg _) (show |x-B|≤(1+|B|)*|x| by linarith only [h,hg]) k
    rw [mul_pow] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (by linarith) hK)

private lemma odd_integral (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F) (k : ℕ) :
    (∫ x : ℝ, (x-diagonalConstant)^(2*k+1) ∂(haarLaw F:Measure ℝ))=0 := by
  let μ := haarLaw F
  let B := diagonalConstant
  let g (x : ℝ) := (x-B)^(2*k+1)
  have hs : reflectedLaw B μ=μ := law_symmetric hAP hF
  have hid (x : ℝ) : g (2*B-x)= -g x := by
    dsimp [g]; rw [show 2*B-x-B= -(x-B) by ring,Odd.neg_pow (⟨k,rfl⟩ : Odd (2*k+1))]
  have hh : (∫ x, g x ∂(μ:Measure ℝ))= -(∫ x, g x ∂(μ:Measure ℝ)) := calc
    _ = ∫ x, g x ∂(reflectedLaw B μ:Measure ℝ) := by rw [hs]
    _ = ∫ x, g (2*B-x) ∂(μ:Measure ℝ) := by
      rw [reflectedLaw,ProbabilityMeasure.toMeasure_map,integral_map (by fun_prop) (by dsimp [g]; fun_prop)]
    _ = _ := by simp_rw [hid]; rw [integral_neg]
  change (∫ x, g x ∂(μ:Measure ℝ))=0
  linarith only [hh]

/-- Every centered odd moment tends to zero, both globally and in each dyadic class. -/
theorem odd_centered_moments (hAP : ProgressionMangoldt) (k : ℕ) :
    Tendsto (primeMean (fun p => (residual p-diagonalConstant)^(2*k+1))) atTop (𝓝 0) ∧
    ∀ {l r : ℕ}, r.Coprime (2^l) → r<2^l →
      Tendsto (progressionMean (2^l) r (fun p => (residual p-diagonalConstant)^(2*k+1))) atTop (𝓝 0) := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  have h := (prime_polynomial_growth hAP hF (by fun_prop) (centered_growth diagonalConstant (2*k+1))).2
  rw [odd_integral hAP hF] at h
  refine ⟨h,?_⟩; intro l r hr hl
  have hd := dyadic_polynomial_growth hAP hF hr hl (by fun_prop) (centered_growth diagonalConstant (2*k+1))
  rwa [odd_integral hAP hF] at hd

end
end Arxiv.«2501.03234».ThetaResidualMoments
#print axioms Arxiv.«2501.03234».ThetaResidualMoments.prime_and_limit_tails
#print axioms Arxiv.«2501.03234».ThetaResidualMoments.exponential_square_root
#print axioms Arxiv.«2501.03234».ThetaResidualMoments.prime_polynomial_growth
#print axioms Arxiv.«2501.03234».ThetaResidualMoments.dyadic_polynomial_growth
#print axioms Arxiv.«2501.03234».ThetaResidualMoments.odd_centered_moments
