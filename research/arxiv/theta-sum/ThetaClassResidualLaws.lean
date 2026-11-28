import ThetaShortConditionalTests

/-! The conditional Haar laws are already the ordinary fixed-class
limits. Every such law has full real support and every dyadic class has
the original law. -/
namespace Arxiv.«2501.03234».ThetaClassResidualLaws
open Filter Real Finset MeasureTheory ThetaShortConditionalLaw ThetaShortClassMeans
open ThetaConditionalHaar ThetaProfiniteUnits ThetaCharacterPrimeMeans ThetaPrimeLaw
open ThetaNaturalPrimeMeans ThetaDyadicLaw ThetaPrimeDensity ThetaIdentityFiber ThetaLocalIntervalTests
open scoped Topology NNReal
noncomputable section

theorem ordinary (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    Tendsto (progressionLaw q r residual) atTop (𝓝 (law F (positive hAP hq hr hu))) := by
  let μ := law F (positive hAP hq hr hu)
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hden := class_prime_density hAP hq hu hr
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro ψ _ ⟨K,hp⟩
  let d := 1/(q.totient:ℝ)
  have hd : 0<d := by dsimp [d];positivity
  have h := weighted (r:=r) hAP hq hF hp
  have eq := scaled_integral F (positive hAP hq hr hu) hp.continuous
  rw [mass hAP hq hr hu] at eq
  rw [←eq] at h
  have H := h.div hden hd.ne'
  rw [mul_comm (1/(q.totient:ℝ)),mul_div_cancel_right₀ _ hd.ne'] at H
  apply H.congr'
  filter_upwards [hden.eventually_const_lt hd,class_nonempty hAP hq hu hr] with X hx hne
  simp only [Pi.div_apply]
  rw [prefix_mean,progression_integral hne residual hp.continuous.measurable,mul_comm,mul_div_cancel_right₀ _ (ne_of_gt hx)]

theorem dyadic (hAP : ProgressionMangoldt) {m r : ℕ} (hr : r<2^m) (hu : r.Coprime (2^m))
    {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    law F (positive hAP (by positivity) hr hu)=haarLaw F :=
  tendsto_nhds_unique (ordinary hAP (by positivity) hr hu hF) (progression_law_tendsto hAP hu hr hF)

theorem full_support (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) (y : ℝ) {d : ℝ} (hd : 0<d) :
    0<(law F (positive hAP hq hr hu) : Measure ℝ) (Metric.ball y d) := by
  classical
  let μ := law F (positive hAP hq hr hu)
  let φ := tent y d
  have hφ : LipschitzWith 1 φ := by simpa only [sub_zero] using lip y d 0
  have h := weighted (r:=r) hAP hq hF hφ
  obtain ⟨δ,hδ,H⟩ := ThetaFullResidualSupport.density hAP hq hr hu y (half_pos hd)
  let f (p : ℕ) := selectClass r q p*φ (residual p)
  have hn (p : ℕ) : 0≤f p := by dsimp [f,selectClass,φ,tent];split_ifs <;> positivity
  have he : ∀ᶠ X : ℕ in atTop,δ*(d/2)≤primeMean f X := by
    filter_upwards [H,Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ)] with X hx hX
    let s := ThetaFullResidualSupport.hits q r y (d/2) X
    have hp : 0<(X.primeCounting:ℝ) := by exact_mod_cast hX
    have hmemb (p : ℕ) : p∈s ↔ p∈Nat.primesLE X ∧ p%q=r ∧ |residual p-y|<d/2 := by
      simp only [s,ThetaFullResidualSupport.hits,primeSet,mem_filter]
    have hs : s⊆Nat.primesLE X := fun p hp => ((hmemb p).mp hp).1
    have hm (p : ℕ) (hp : p∈s) : d/2≤f p := by
      have ha : p%q=r ∧ |residual p-y|<d/2 := ((hmemb p).mp hp).2
      simp only [f,selectClass,ha.1,if_true,one_mul,φ,tent]
      exact le_trans (by linarith only [ha.2] : d/2≤d-|residual p-y|) (le_max_right ..)
    have hh := sum_le_sum hm
    simp only [sum_const,nsmul_eq_mul] at hh
    apply (le_div_iff₀ hp).mpr
    have hs' := sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => hn p)
    change δ*X.primeCounting≤(s.card:ℝ) at hx
    nlinarith only [hh,hs',mul_le_mul_of_nonneg_right hx (half_pos hd).le]
  have hpos := (mul_pos hδ (half_pos hd)).trans_le (ge_of_tendsto h he)
  have eq := scaled_integral F (positive hAP hq hr hu) hφ.continuous
  by_contra! hc
  have hz : (μ:Measure ℝ) (Metric.ball y d)=0 := nonpos_iff_eq_zero.mp hc
  have hzero : (∫ x,φ x ∂μ)=0 := by
    apply integral_eq_zero_of_ae
    have hh : ∀ᵐ x ∂(μ:Measure ℝ),x∉Metric.ball y d := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
    filter_upwards [hh] with x hx
    have hn := le_of_not_gt (show ¬|x-y|<d by simpa only [Metric.mem_ball,Real.dist_eq] using hx)
    exact max_eq_left (sub_nonpos.mpr hn)
  change haar.real (fibre q r)*(∫ x,φ x ∂μ)=_ at eq
  rw [hzero,mul_zero] at eq
  exact hpos.ne' eq.symm

theorem odd_part (hAP : ProgressionMangoldt) {q k b : ℕ} (hq : Odd q)
    (hb : b<2^k*q) (hu : b.Coprime (2^k*q)) {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    ∃ hc : haar (fibre q (b%q))≠0,law F (positive hAP (by omega : 0<2^k*q) hb hu)=law F hc := by
  have hq' : 0<q := by exact Nat.pos_of_ne_zero (by rintro rfl;simp at hq)
  have hd : 0<2^k := by positivity
  have hp : (2^k).Coprime q := (Nat.coprime_two_left.mpr hq).pow_left _
  obtain ⟨hc₁,hc₂⟩ := Nat.coprime_mul_iff_right.mp hu
  have h₁ : (b%(2^k)).Coprime (2^k) := by simpa only [Nat.Coprime,←Nat.gcd_rec (2^k) b] using hc₁.symm
  have h₂ : (b%q).Coprime q := by simpa only [Nat.Coprime,←Nat.gcd_rec q b] using hc₂.symm
  have hr := Nat.mod_lt b hq'
  let hc := positive hAP hq' hr h₂
  refine ⟨hc,?_⟩
  apply tendsto_nhds_unique (ordinary hAP (Nat.mul_pos hd hq') hb hu hF)
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro ψ hbound ⟨K,hψ⟩
  obtain ⟨C,hC⟩ := hbound
  let g : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound ⟨ψ,hψ.continuous⟩ C hC
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (ordinary hAP hq' hr h₂ hF) g
  have hbase : Tendsto (progressionMean q (b%q) (fun p => ψ (residual p))) atTop (𝓝 (∫ x,ψ x ∂(law F hc))) :=
    hlim.congr' ((class_nonempty hAP hq' h₂ hr).mono (fun X hx => progression_integral hx residual hψ.continuous.measurable))
  have hm := mixed_restriction hAP h₁ (Nat.mod_lt b hd) hq h₂ hr hψ hbase
  apply hm.congr'
  filter_upwards [class_nonempty hAP (Nat.mul_pos hd hq') hu hb] with X hx
  rw [progression_integral hx residual hψ.continuous.measurable]
  have hset : primeSet (fun n => n%2^k=b%2^k ∧ n%q=b%q) X=primeSet (fun n => n%(2^k*q)=b) X := by
    ext p
    simp only [primeSet,mem_filter]
    apply and_congr_right;intro _
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hb] using (Nat.modEq_and_modEq_iff_modEq_mul (a:=p) (b:=b) hp)
  simp only [mixedMean,progressionMean,hset]

theorem ordinary_tests (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {φ : ℝ → ℝ} (hp : Continuous φ)
    {K : ℝ} (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k)) :
    Tendsto (progressionMean q r (fun p => φ ((S p:ℝ)/p-log p/2))) atTop
      (𝓝 (∫ x,φ x ∂(law F (positive hAP hq hr hu)))) := by
  let s (X : ℕ) := primeSet (fun n => n%q=r) X
  let I := ∫ x : ℝ,x^(k*2) ∂(haarLaw F)
  let b := |I|+1
  have hb : 0<b := by dsimp [b];positivity
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hM := (ThetaResidualMoments.prime_polynomial_growth hAP hF (φ:=fun x : ℝ => x^(k*2)) (continuous_pow _)
    (K:=1) (k:=k*2) (fun x => by rw [←pow_abs];linarith only [pow_nonneg (abs_nonneg x) (k*2)])).2
  have hx := hM.eventually_le_const (show I<b by dsimp [b];linarith only [le_abs_self I])
  have hd := (class_prime_density hAP hq hu hr).eventually_const_lt
    (show 1/(2*(q.totient:ℝ))<1/q.totient by apply one_div_lt_one_div_of_lt hφ;linarith)
  have hs := class_nonempty hAP hq hu hr
  have H : ∀ᶠ X : ℕ in atTop,mean (s X) (fun p => (residual p)^(k*2))≤b*(2*q.totient) := by
    filter_upwards [hs,hx,hd,Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ)] with X hpop h₁ h₂ hX
    have hX' : 0<(X.primeCounting:ℝ) := by exact_mod_cast hX
    have hcard := (lt_div_iff₀ hX').mp h₂
    have heq : (1/(2*(q.totient:ℝ)))*X.primeCounting=X.primeCounting/(2*(q.totient:ℝ)) := by ring
    rw [heq] at hcard
    have hnum := (div_lt_iff₀ (by positivity : 0<2*(q.totient:ℝ))).mp hcard
    have hsub : s X⊆Nat.primesLE X := by
      intro p hp;simp only [s,primeSet,mem_filter] at hp;exact hp.1
    have hc : ((Nat.primesLE X).card:ℝ)≤(2*q.totient)*(s X).card := by
      rw [Nat.primesLE_card_eq_primeCounting,mul_comm];exact hnum.le
    apply dominated hpop hsub (fun p => by rw [pow_mul];exact sq_nonneg _) hc hb.le
    simpa only [mean,Nat.primesLE_card_eq_primeCounting,primeMean] using h₁
  have hw := ordinary hAP hq hr hu hF
  have hi := ThetaShortConditionalTests.integrable F (positive hAP hq hr hu) hp
    (ThetaResidualMoments.prime_polynomial_growth hAP hF hp hg).1
  apply ThetaWindowTruncation.limit (s:=s) (r:=residual) hp k hg hi (by positivity) (hs.and H)
  intro ψ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw ψ).congr'
    (hs.mono (fun X hX => progression_integral hX residual ψ.continuous.measurable))

#print axioms ordinary_tests

/-- One Haar representative describes all the fixed-class short-window laws. -/
def Windows (θ : ℝ) := ∃ F : G →₁[haar] ℝ,Represents residual F ∧
  ∀ q r : ℕ,0<q → r<q → r.Coprime q → ∃ hc : haar (fibre q r)≠0,
    (∀ y : ℝ,∀ d>0,0<(law F hc : Measure ℝ) (Metric.ball y d)) ∧
    ∀ H : ℕ → ℕ,(∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X) →
      Tendsto (fun X => ThetaWindowClassMeasure.law (window q r X (H X))) atTop (𝓝 (law F hc)) ∧
      ∀ φ : ℝ → ℝ,Continuous φ → ∀ K : ℝ,∀ k : ℕ,(∀ x,|φ x|≤K*(1+|x|^k)) →
        Tendsto (fun X => mean (window q r X (H X)) (fun p => φ ((S p:ℝ)/p-log p/2))) atTop
          (𝓝 (∫ x,φ x ∂(law F hc)))

theorem windows {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : ThetaCalibratedCone.Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : ThetaLocalPrimeCounts.Ordinary θ) (hAP : ProgressionMangoldt) :
    Windows θ := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  refine ⟨F,hF,?_⟩
  intro q r hq hr hu
  refine ⟨positive hAP hq hr hu,fun y _ hd => full_support hAP hq hr hu hF y hd,?_⟩
  intro H hh
  exact ⟨ThetaShortConditionalLaw.weak he h48 hk hθ hθ₁ h hAP hq hr hu hF hh,
    fun _ hp _ k hg => ThetaShortConditionalTests.original he h48 hk hθ hθ₁ h hAP hq hr hu hF hh hp k hg⟩

#print axioms windows

#print axioms odd_part

#print axioms ordinary
#print axioms dyadic
#print axioms full_support
end
end Arxiv.«2501.03234».ThetaClassResidualLaws
