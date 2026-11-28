import ThetaPrimeResidualLaw

/-! Independence of the dyadic prime class from the theta residual and odd periodic data. -/
namespace Arxiv.«2501.03234».ThetaDyadicLaw
open Finset Filter MeasureTheory ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans
open ThetaCharacterPrimeMeans ThetaCharacterCoefficient ThetaDiagonalConstant ThetaPeriodMeans
open ThetaConditionalRows ThetaPrimeTailTransfer ThetaPrimeDensity
open scoped Topology NNReal
noncomputable section

private lemma odd_model_period (T V : ℕ) : ∃ M : ℕ, Odd M ∧ OnMod M (residualModel T V) := by
  classical
  let s := (Icc 2 T).filter Odd
  let M := ∏ d∈s,d
  have hM : Odd M := Finset.prod_induction (s:=s) id Odd (fun _ _ => Odd.mul) (by decide)
    (fun _ hd => (mem_filter.mp hd).2)
  have hdM (d) (hd : d∈Icc 2 T) (ho : Odd d) : d∣M := dvd_prod_of_mem id (mem_filter.mpr ⟨hd,ho⟩)
  have hm : OnMod M (model T V) := low_onMod hdM _ _
  exact ⟨M,hM,fun n => by simp only [residualModel,hm n]⟩

private lemma product_period {a b : ℕ} {f g : ℕ → ℝ} (hf : OnMod a f) (hg : OnMod b g) :
    OnMod (a*b) (fun n => f n*g n) := by
  intro n
  exact congrArg₂ (·*·) (onMod_lift (Nat.dvd_mul_right a b) hf n) (onMod_lift (Nat.dvd_mul_left b a) hg n)

private lemma periodic_bound {d : ℕ} (hd : 0 < d) {f : ℕ → ℝ} (hf : OnMod d f) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, |f n| ≤ D := by
  refine ⟨∑ i∈range d,|f i|,sum_nonneg (fun _ _ => abs_nonneg _),fun n => ?_⟩
  rw [← hf n]
  exact single_le_sum (fun i _ => abs_nonneg (f i)) (mem_range.mpr (Nat.mod_lt _ hd))

private lemma model_zero (hAP : ProgressionMangoldt) (k T V : ℕ) {h w : ℕ → ℝ}
    (hh : OnMod (2^k) h) (h0 : unitMean (2^k) h=0) {m : ℕ} (hm : Odd m) (hw : OnMod m w)
    (φ : ℝ → ℝ) :
    Tendsto (primeMean (fun p => h p*w p*φ (residualModel T V p))) atTop (𝓝 0) := by
  obtain ⟨M,hM,hg⟩ := odd_model_period T V
  let : NeZero (m*M) := ⟨(hm.mul hM).pos.ne'⟩
  let f (n : ℕ) := w n*φ (residualModel T V n)
  have hf : OnMod (m*M) f := product_period hw (fun n => congrArg φ (hg n))
  have H := periodic_prime_mean hAP (product_period hh hf)
  have hc : (2^k).Coprime (m*M) := (hm.mul hM).coprime_two_left.pow_left k
  rw [unitMean_mul hc hh hf,h0,zero_mul] at H
  simpa only [f,mul_assoc] using H

private lemma test_error (u : ℕ → ℝ) {D : ℝ} (hu : ∀ n, |u n| ≤ D) (f g : ℕ → ℝ)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) (X : ℕ) :
    |primeMean (fun p => u p*φ (f p)) X - primeMean (fun p => u p*φ (g p)) X| ≤
      (D*K)*primeMean (fun p => |f p-g p|) X := by
  unfold primeMean
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) X.primeCounting),
    ← sum_sub_distrib,← mul_div_assoc,mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro p _
  rw [← mul_sub,abs_mul,mul_assoc]
  exact mul_le_mul (hu p) (hp.dist_le_mul (f p) (g p)) (abs_nonneg _) ((abs_nonneg _).trans (hu p))

/-- A centered dyadic weight has zero limiting prime correlation with the
residual even after weighting by any fixed odd-period function. -/
theorem dyadic_orthogonality (hAP : ProgressionMangoldt) (k : ℕ) {h w : ℕ → ℝ}
    (hh : OnMod (2^k) h) (h0 : unitMean (2^k) h=0) {m : ℕ} (hm : Odd m) (hw : OnMod m w)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) :
    Tendsto (primeMean (fun p => h p*w p*φ (residual p))) atTop (𝓝 0) := by
  let u (n : ℕ) := h n*w n
  obtain ⟨D,hD,hu⟩ := periodic_bound (Nat.mul_pos (show 0<2^k by positivity) hm.pos) (product_period hh hw)
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let η := ε/(D*K+2)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨T,V,he'⟩ := residual_model_approximation hη
  have hz := model_zero hAP k T V hh h0 hm hw φ
  filter_upwards [he',Metric.tendsto_nhds.mp hz η hη] with X h₁ h₂
  have htri := dist_triangle (primeMean (fun p => u p*φ (residual p)) X)
    (primeMean (fun p => u p*φ (residualModel T V p)) X) 0
  have H := (test_error u hu residual (residualModel T V) hp X).trans
    (mul_le_mul_of_nonneg_left h₁ (mul_nonneg hD K.2))
  have heq : (D*K+2)*η=ε := by dsimp [η]; field_simp
  rw [← Real.dist_eq] at H
  dsimp only [u] at htri H
  linarith only [htri,h₂,H,heq,hη]

#print axioms dyadic_orthogonality

/-- Ordinary mean inside a prime progression, normalized by its own count. -/
def progressionMean (q r : ℕ) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ p ∈ primeSet (fun n => n%q=r) X, f p) / (primeSet (fun n => n%q=r) X).card

private def select (q r n : ℕ) : ℝ := if n%q=r then 1 else 0

private theorem select_periodic (q r : ℕ) : OnMod q (select q r) := by intro n; simp [select]

private theorem selected_sum (q r X : ℕ) (f : ℕ → ℝ) :
    (∑ p∈Nat.primesLE X,select q r p*f p) = ∑ p∈primeSet (fun n => n%q=r) X,f p := by
  rw [primeSet,sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases h : p%q=r <;> simp [select,h]

private lemma select_model_mean (hAP : ProgressionMangoldt) {q r : ℕ} [NeZero q]
    (hr : r.Coprime q) (hlt : r<q) : unitMean q (select q r) = 1/(q.totient:ℝ) := by
  have h := class_prime_density hAP (NeZero.pos q) hr hlt
  have hsel : Tendsto (primeMean (select q r)) atTop (𝓝 (1/(q.totient:ℝ))) := by
    apply h.congr'
    apply Eventually.of_forall
    intro X
    have H := selected_sum q r X (fun _ => (1:ℝ))
    simp only [mul_one,sum_const,nsmul_eq_mul] at H
    exact congrArg (·/(X.primeCounting:ℝ)) H.symm
  exact tendsto_nhds_unique (periodic_prime_mean hAP (select_periodic q r)) hsel

private lemma centered_zero (q : ℕ) [NeZero q] (v : ℕ → ℝ) :
    unitMean q (fun p => v p-unitMean q v) = 0 := by
  have hp : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [unitMean,sum_sub_distrib,sum_const,card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul]
  field_simp
  ring

/-- Every fixed odd-period weighted Lipschitz mean with an all-prime
limit has the same limit inside each reduced dyadic progression. -/
theorem dyadic_restriction (hAP : ProgressionMangoldt) {k r m : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) (hm : Odd m) {w : ℕ → ℝ} (hw : OnMod m w)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) {A : ℝ}
    (hA : Tendsto (primeMean (fun p => w p*φ (residual p))) atTop (𝓝 A)) :
    Tendsto (progressionMean (2^k) r (fun p => w p*φ (residual p))) atTop (𝓝 A) := by
  let q := 2^k
  let : NeZero q := ⟨by dsimp [q]; positivity⟩
  let v := select q r
  let c := unitMean q v
  let h (p : ℕ) := v p-c
  let f (p : ℕ) := w p*φ (residual p)
  have hc : c = 1/(q.totient:ℝ) := select_model_mean hAP hr hlt
  have hc' : c ≠ 0 := by rw [hc]; exact one_div_ne_zero (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  have hper : OnMod q h := fun n => congrArg (·-c) (select_periodic q r n)
  have hz := dyadic_orthogonality hAP k hper (centered_zero q v) hm hw hp
  have H := hz.add (hA.const_mul c)
  rw [zero_add] at H
  have hnum : Tendsto (fun X => (∑ p∈primeSet (fun n => n%q=r) X, f p)/X.primeCounting) atTop (𝓝 (c*A)) := by
    apply H.congr'
    apply Eventually.of_forall
    intro X
    dsimp only []
    rw [← selected_sum q r X f]
    simp only [primeMean,← mul_div_assoc,← add_div]
    congr 1
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    dsimp [h,f,v]
    ring
  have hden := class_prime_density hAP (NeZero.pos q) hr hlt
  rw [← hc] at hden
  have ha := hnum.div hden hc'
  rw [mul_div_cancel_left₀ A hc'] at ha
  apply ha.congr'
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_ne_atTop 0] with X hX
  dsimp only [Pi.div_apply,progressionMean,f,q]
  change (X.primeCounting:ℝ) ≠ 0 at hX
  field_simp

#print axioms dyadic_restriction

/-- Conditional samples use the singleton at 2 until the first prime in the class. -/
private def classSample (q r X : ℕ) : Finset ℕ := by
  classical
  exact if (primeSet (fun n => n%q=r) X).Nonempty then primeSet (fun n => n%q=r) X else {2}

private instance (q r X : ℕ) : Nonempty ↥(classSample q r X) := by
  classical
  unfold classSample
  split_ifs with h
  · exact h.to_subtype
  · exact ⟨⟨2,by simp⟩⟩

private def uniformClass (q r X : ℕ) : ProbabilityMeasure ↥(classSample q r X) :=
  ⟨(PMF.uniformOfFintype _).toMeasure,inferInstance⟩

/-- The empirical probability law in one progression, normalized by its own prime count. -/
def progressionLaw (q r : ℕ) (f : ℕ → ℝ) (X : ℕ) : ProbabilityMeasure ℝ :=
  (uniformClass q r X).map (f:=fun p => f p.val) (measurable_of_countable _).aemeasurable

private lemma progression_integral {q r X : ℕ} (h : (primeSet (fun n => n%q=r) X).Nonempty)
    (f : ℕ → ℝ) {φ : ℝ → ℝ} (hp : Measurable φ) :
    (∫ x, φ x ∂(progressionLaw q r f X)) = progressionMean q r (fun p => φ (f p)) X := by
  rw [progressionLaw,ProbabilityMeasure.toMeasure_map,integral_map (measurable_of_countable _).aemeasurable
    hp.aestronglyMeasurable]
  change (∫ p : ↥(classSample q r X), φ (f p.val) ∂(PMF.uniformOfFintype _).toMeasure) = _
  rw [PMF.integral_eq_sum]
  have hs : (∑ p : ↥(classSample q r X),φ (f p.val)) = ∑ p∈classSample q r X,φ (f p) :=
    Finset.sum_attach (classSample q r X) (fun p => φ (f p))
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,
    ← mul_sum,hs,Fintype.card_coe,progressionMean,div_eq_inv_mul]
  rw [show classSample q r X = primeSet (fun n => n%q=r) X from if_pos h]

private lemma class_nonempty (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q)
    (hr : r.Coprime q) (hlt : r<q) : ∀ᶠ X in atTop,(primeSet (fun n => n%q=r) X).Nonempty := by
  have h := (class_prime_density hAP hq hr hlt).eventually_const_lt
    (show (0:ℝ)<1/(q.totient:ℝ) by have := Nat.totient_pos.mpr hq; positivity)
  filter_upwards [h] with X hX
  apply card_pos.mp
  by_contra! hz
  have he := Nat.eq_zero_of_le_zero hz
  simp [he] at hX

/-- Every reduced dyadic progression has the same limits for Lipschitz residual tests. -/
theorem progression_lipschitz (hAP : ProgressionMangoldt) {k r : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) :
    Tendsto (progressionMean (2^k) r (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ x ∂(haarLaw F))) := by
  have hA := prime_mean_lipschitz hAP hF hp
  rw [← haarLaw_integral F hp.continuous] at hA
  simpa only [one_mul] using (dyadic_restriction hAP hr hlt (m:=1) (by decide)
    (w:=fun _ => 1) (fun _ => rfl) hp (by simpa only [one_mul] using hA))

/-- The weak limit in every reduced dyadic class is the full all-prime residual law. -/
theorem progression_law_tendsto (hAP : ProgressionMangoldt) {k r : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    Tendsto (progressionLaw (2^k) r residual) atTop (𝓝 (haarLaw F)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ _ ⟨K,hK⟩
  exact (progression_lipschitz hAP hr hlt hF hK).congr' ((class_nonempty hAP (by positivity) hr hlt).mono
    fun X hX => (progression_integral hX residual hK.continuous.measurable).symm)

#print axioms progression_lipschitz
#print axioms progression_law_tendsto

/-- One symmetric law describes every dyadic prime progression simultaneously. -/
theorem S_dyadic_laws (hAP : ProgressionMangoldt) :
    ∃ F : G →₁[haar] ℝ, Represents residual F ∧
      reflectedLaw diagonalConstant (haarLaw F) = haarLaw F ∧
      ∀ k r : ℕ, r.Coprime (2^k) → r < 2^k →
        Tendsto (progressionLaw (2^k) r residual) atTop (𝓝 (haarLaw F)) ∧
        ∀ (φ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K φ →
          Tendsto (progressionMean (2^k) r (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ x ∂(haarLaw F))) := by
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  exact ⟨F,hF,law_symmetric hAP hF,fun _ _ hr hlt => ⟨progression_law_tendsto hAP hr hlt hF,
    fun _ _ hp => progression_lipschitz hAP hr hlt hF hp⟩⟩

#print axioms S_dyadic_laws

/-- Prime average subject to simultaneous dyadic and odd congruences. -/
def mixedMean (q r m a : ℕ) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  let s := primeSet (fun n => n%q=r ∧ n%m=a) X
  (∑ p∈s,f p)/s.card

private lemma selected_inside (q r m a X : ℕ) (f : ℕ → ℝ) :
    (∑ p∈primeSet (fun n => n%q=r) X, select m a p*f p) =
      ∑ p∈primeSet (fun n => n%q=r ∧ n%m=a) X, f p := by
  classical
  simp only [primeSet,sum_filter,select]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp_all

/-- Any Lipschitz-test mean known in an odd residue class is preserved under
further restriction to a reduced dyadic class. Both means use their own counts. -/
theorem mixed_restriction (hAP : ProgressionMangoldt) {k r m a : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) (hm : Odd m) (ha : a.Coprime m) (hat : a < m)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hp : LipschitzWith K φ) {A : ℝ}
    (hA : Tendsto (progressionMean m a (fun p => φ (residual p))) atTop (𝓝 A)) :
    Tendsto (mixedMean (2^k) r m a (fun p => φ (residual p))) atTop (𝓝 A) := by
  let q := 2^k
  let f (p : ℕ) := φ (residual p)
  let c := 1/(m.totient:ℝ)
  have hc : c ≠ 0 := by dsimp [c]; exact one_div_ne_zero (by exact_mod_cast (Nat.totient_pos.mpr hm.pos).ne')
  have hden := class_prime_density hAP hm.pos ha hat
  have H := hA.mul hden
  have hnum : Tendsto (primeMean (fun p => select m a p*f p)) atTop (𝓝 (A*c)) := by
    apply H.congr'
    filter_upwards [class_nonempty hAP hm.pos ha hat] with X hX
    have hpos : ((primeSet (fun n => n%m=a) X).card:ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
    dsimp only [progressionMean,primeMean,Pi.mul_apply]
    rw [selected_sum]
    field_simp
    rfl
  have hn := dyadic_restriction hAP hr hlt hm (select_periodic m a) hp hnum
  let : NeZero m := ⟨hm.pos.ne'⟩
  have hw := periodic_prime_mean hAP (select_periodic m a)
  rw [select_model_mean hAP ha hat] at hw
  have hd := dyadic_restriction hAP hr hlt hm (select_periodic m a)
    (φ:=fun _ => (1:ℝ)) (LipschitzWith.const 1) (by simpa only [mul_one] using hw)
  simp only [mul_one] at hd
  have ha' := hn.div hd hc
  rw [mul_div_cancel_right₀ A hc] at ha'
  apply ha'.congr'
  filter_upwards [class_nonempty hAP (by positivity) hr hlt] with X hX
  have hpos : ((primeSet (fun n => n%q=r) X).card:ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
  have he := selected_inside q r m a X (fun _ => (1:ℝ))
  simp only [mul_one,sum_const,nsmul_eq_mul] at he
  dsimp only [Pi.div_apply,progressionMean,mixedMean]
  rw [selected_inside,he]
  exact div_div_div_cancel_right₀ hpos _ _

/-- The exact signed modulo-three means B+C and B−C persist inside every
reduced dyadic progression, in particular for the two subclasses of 1 mod 8. -/
theorem dyadic_mod_three_means (hAP : ProgressionMangoldt) {k r : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r<2^k) :
    Tendsto (mixedMean (2^k) r 3 1 residual) atTop (𝓝 (diagonalConstant+characterConstant)) ∧
      Tendsto (mixedMean (2^k) r 3 2 residual) atTop (𝓝 (diagonalConstant-characterConstant)) := by
  obtain ⟨_,_,h1,h2,_⟩ := prime_class_statistics_exact hAP
  exact ⟨mixed_restriction hAP hr hlt (by decide : Odd 3) (by decide : Nat.Coprime 1 3)
    (by decide) LipschitzWith.id h1,
    mixed_restriction hAP hr hlt (by decide : Odd 3) (by decide : Nat.Coprime 2 3)
      (by decide) LipschitzWith.id h2⟩

#print axioms mixed_restriction
#print axioms dyadic_mod_three_means

private def predicateMean (P : ℕ → Prop) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ p∈primeSet P X,f p)/(primeSet P X).card

private lemma above_mean_density (P : ℕ → Prop) (hP : PositiveLowerPrimeDensity P)
    {s L a : ℝ} (hs : |s|=1) (ha : a<L)
    (hL : Tendsto (predicateMean P (fun p => s*residual p)) atTop (𝓝 L)) :
    PositiveLowerPrimeDensity (fun p => P p ∧ a < s*residual p) := by
  classical
  obtain ⟨δ,hδ,hP'⟩ := hP
  let e := (L-a)/2
  have he : 0<e := half_pos (sub_pos.mpr ha)
  have he' : a+e < L := by dsimp [e]; linarith
  obtain ⟨T,V,H⟩ := residual_model_approximation (show 0<e*δ/2 by positivity)
  obtain ⟨M,hM,hB⟩ := periodic_bound (Nat.factorial_pos T) (residualModel_periodic T V)
  let D := M+|a|+1
  have hD : 0<D := by dsimp [D]; positivity
  let f (p : ℕ) := s*residual p
  let err (p : ℕ) := |residual p-residualModel T V p|
  have hpoint (p : ℕ) : f p-a ≤ (if a<f p then D else 0)+err p := by
    split_ifs with h
    · have h₁ := le_abs_self (s*(residual p-residualModel T V p))
      have h₂ := le_abs_self (s*residualModel T V p)
      rw [abs_mul,hs,one_mul] at h₁ h₂
      dsimp only [D,f,err]
      nlinarith only [h₁,h₂,hB p,neg_abs_le a]
    · dsimp only [err]
      linarith only [le_of_not_gt h,abs_nonneg (residual p-residualModel T V p)]
  refine ⟨(e*δ/2)/D,by positivity,?_⟩
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [H,hP',hL.eventually_const_lt he',hπ.eventually_gt_atTop 0] with X hE hPX hL' hX
  let U := primeSet P X
  let A := primeSet (fun p => P p ∧ a<f p) X
  change (0:ℝ)<X.primeCounting at hX
  change δ * (X.primeCounting:ℝ) ≤ (U.card:ℝ) at hPX
  have hcard : (0:ℝ)<U.card := (mul_pos hδ hX).trans_le hPX
  change a+e < (∑ p∈U,f p)/(U.card:ℝ) at hL'
  have hLo := (lt_div_iff₀ hcard).mp hL'
  change (∑ p∈X.primesLE,err p)/(X.primeCounting:ℝ) ≤ e*δ/2 at hE
  have hErr := (div_le_iff₀ hX).mp hE
  have hU : U ⊆ X.primesLE := filter_subset _ _
  have hAll := sum_le_sum_of_subset_of_nonneg hU (fun p _ _ => abs_nonneg (residual p-residualModel T V p))
  change (∑ p∈U,err p) ≤ ∑ p∈X.primesLE,err p at hAll
  have hbound := sum_le_sum (s:=U) (fun p _ => hpoint p)
  rw [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul] at hbound
  have hAf : U.filter (fun p => a<f p) = A := by
    ext p
    simp [U,A,primeSet,and_assoc]
  have hcnt : (∑ p∈U,if a<f p then D else 0) = A.card*D := by
    rw [← sum_filter,hAf,sum_const,nsmul_eq_mul]
  rw [hcnt] at hbound
  change ((e*δ/2)/D)*X.primeCounting ≤ (A.card:ℝ)
  rw [div_mul_eq_mul_div,div_le_iff₀ hD]
  nlinarith only [hLo,hbound,hAll,hErr,mul_le_mul_of_nonneg_left hPX he.le]

private lemma mixed_class_density (hAP : ProgressionMangoldt) {k r m a : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r < 2^k) (hm : Odd m) (ha : a.Coprime m) (hat : a < m) :
    PositiveLowerPrimeDensity (fun p => p%2^k=r ∧ p%m=a) := by
  classical
  let q := 2^k
  let : NeZero m := ⟨hm.pos.ne'⟩
  let : NeZero q := ⟨by dsimp [q]; positivity⟩
  have hc : q.Coprime m := hm.coprime_two_left.pow_left k
  have hp := periodic_prime_mean hAP (product_period (select_periodic q r) (select_periodic m a))
  rw [unitMean_mul hc (select_periodic q r) (select_periodic m a),select_model_mean hAP hr hlt,
    select_model_mean hAP ha hat] at hp
  let d := 1/(q.totient:ℝ)*(1/(m.totient:ℝ))
  have hd : 0<d := by
    have := Nat.totient_pos.mpr (NeZero.pos q)
    have := Nat.totient_pos.mpr hm.pos
    dsimp [d]
    positivity
  refine ⟨d/2,half_pos hd,?_⟩
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hp.eventually_const_lt (half_lt_self hd),hπ.eventually_gt_atTop 0] with X H hX
  change d/2 < (∑ p∈X.primesLE, select q r p*select m a p)/(X.primeCounting:ℝ) at H
  rw [selected_sum] at H
  have he := selected_inside q r m a X (fun _ => (1:ℝ))
  simp only [mul_one,sum_const,nsmul_eq_mul] at he
  rw [he] at H
  exact ((lt_div_iff₀ hX).mp H).le

/-- The primes in the prescribed joint classes with residual above B+t (class 1)
or below B−t (class 2) each have positive lower density among all primes. -/
theorem dyadic_mod_three_excursions (hAP : ProgressionMangoldt) {k r : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r < 2^k) {t : ℝ} (ht : t < characterConstant) :
    PositiveLowerPrimeDensity (fun p => (p%2^k=r ∧ p%3=1) ∧ diagonalConstant+t < residual p) ∧
    PositiveLowerPrimeDensity (fun p => (p%2^k=r ∧ p%3=2) ∧ residual p < diagonalConstant-t) := by
  obtain ⟨h1,h2⟩ := dyadic_mod_three_means hAP hr hlt
  have hp1 := mixed_class_density hAP hr hlt (by decide : Odd 3) (by decide : Nat.Coprime 1 3) (by decide)
  have hp2 := mixed_class_density hAP hr hlt (by decide : Odd 3) (by decide : Nat.Coprime 2 3) (by decide)
  have H := above_mean_density _ hp1 (s:=1) (by norm_num) (a:=diagonalConstant+t) (L:=diagonalConstant+characterConstant)
    (by linarith) (by
      apply h1.congr'
      exact Eventually.of_forall (fun X => by simp only [predicateMean,mixedMean,one_mul]))
  have hneg : Tendsto (predicateMean (fun p => p%2^k=r ∧ p%3=2) (fun p => -1*residual p)) atTop
      (𝓝 (-(diagonalConstant-characterConstant))) := by
    apply h2.neg.congr'
    apply Eventually.of_forall
    intro X
    simp [predicateMean,mixedMean,← neg_div]
  have J := above_mean_density _ hp2 (s:= -1) (by norm_num) (a:= -(diagonalConstant-t))
    (L:= -(diagonalConstant-characterConstant)) (by linarith) hneg
  simpa only [one_mul,neg_one_mul,neg_lt_neg_iff] using And.intro H J

#print axioms dyadic_mod_three_excursions

private lemma primeDensity_mono {P Q : ℕ → Prop} (h : ∀ p, p.Prime → P p → Q p)
    (H : PositiveLowerPrimeDensity P) : PositiveLowerPrimeDensity Q := by
  classical
  obtain ⟨δ,hδ,hX⟩ := H
  refine ⟨δ,hδ,hX.mono fun X hX => hX.trans ?_⟩
  exact_mod_cast card_le_card (show primeSet P X ⊆ primeSet Q X by
    intro p hp
    obtain ⟨hl,hp'⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hl,h p (Nat.prime_of_mem_primesLE hl) hp'⟩)

/-- In every reduced dyadic class both excursions of the original S(p) have
positive lower density even when normalized by the number of all primes. -/
theorem S_dyadic_reflected_excursions (hAP : ProgressionMangoldt) {k r : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r<2^k) {t : ℝ} (ht : t<characterConstant) :
    PositiveLowerPrimeDensity (fun p => (p%2^k=r ∧ p%3=1) ∧
      p*Real.log p/2+(diagonalConstant+t)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => (p%2^k=r ∧ p%3=2) ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-t)*p) := by
  obtain ⟨hhi,hlo⟩ := dyadic_mod_three_excursions hAP hr hlt ht
  constructor
  · apply primeDensity_mono _ hhi
    rintro p hp ⟨hr',H⟩
    refine ⟨hr',?_⟩
    change diagonalConstant+t < (S p:ℝ)/p-Real.log p/2 at H
    have hp' : (0:ℝ)<p := by exact_mod_cast hp.pos
    have H' := (lt_div_iff₀ hp').mp (lt_sub_iff_add_lt.mp H)
    linarith only [H']
  · apply primeDensity_mono _ hlo
    rintro p hp ⟨hr',H⟩
    refine ⟨hr',?_⟩
    change (S p:ℝ)/p-Real.log p/2 < diagonalConstant-t at H
    have hp' : (0:ℝ)<p := by exact_mod_cast hp.pos
    have H' := (div_lt_iff₀ hp').mp (sub_lt_iff_lt_add.mp H)
    linarith only [H']

#print axioms S_dyadic_reflected_excursions

/-- In the class 1 modulo 8, the upper excursion occurs
on a positive lower fraction of primes at 1 modulo 24, the lower at 17 modulo 24. -/
theorem S_one_mod_eight_excursions (hAP : ProgressionMangoldt) {t : ℝ} (ht : t<characterConstant) :
    PositiveLowerPrimeDensity (fun p => p%24=1 ∧
      p*Real.log p/2+(diagonalConstant+t)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => p%24=17 ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-t)*p) := by
  obtain ⟨h₁,h₂⟩ := S_dyadic_reflected_excursions (k:=3) (r:=1) hAP (by decide) (by decide) ht
  constructor
  · apply primeDensity_mono _ h₁
    rintro p _ ⟨⟨h8,h3⟩,h⟩
    refine ⟨?_,h⟩
    change p%8=1 at h8
    omega
  · apply primeDensity_mono _ h₂
    rintro p _ ⟨⟨h8,h3⟩,h⟩
    refine ⟨?_,h⟩
    change p%8=1 at h8
    omega

#print axioms S_one_mod_eight_excursions

end
end Arxiv.«2501.03234».ThetaDyadicLaw
