import ThetaNaturalPrimeMeans

/-! Character means of the second-order residual in the two prime classes modulo three. -/
namespace Arxiv.«2501.03234».ThetaCharacterPrimeMeans
open Finset Filter ThetaCharacterThree ThetaNaturalPrimeMeans ThetaPrimeTailTransfer
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaReciprocalInversion
open ThetaPrimeMeanSquare
open scoped Topology

private lemma char_bound (p : ℕ) : |(chi p : ℝ)| ≤ 1 := by
  unfold chi
  split_ifs <;> norm_num

/-- Bounded weights preserve the iterated prime mean approximation by reciprocal models. -/
theorem bounded_twist_approx_eventually (w : ℕ → ℝ) (hw : ∀ p, |w p| ≤ 1) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, ∀ᶠ V : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      |primeMean (fun p => w p*scaledOff p) X -
       primeMean (fun p => w p*model T V p) X| ≤ ε := by
  filter_upwards [prime_model_absolute_eventually he] with T hT
  filter_upwards [hT] with V H
  have hπ : Tendsto (fun N : ℕ => (N.primeCounting : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  filter_upwards [H,hπ.eventually_gt_atTop 0] with X hX hx
  rw [primeMean,primeMean,← sub_div,← sum_sub_distrib,abs_div,abs_of_pos hx,div_le_iff₀ hx]
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun p _ => ?_)).trans hX)
  rw [← mul_sub,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hw p)

/-- Every sufficiently large pair of successive cutoffs approximates the
prime character mean. The cutoffs tend to infinity in the stated order. -/
theorem twisted_approx_eventually {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, ∀ᶠ V : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      |primeMean (fun p => (chi p : ℝ)*scaledOff p) X -
       primeMean (fun p => (chi p : ℝ)*model T V p) X| ≤ ε :=
  bounded_twist_approx_eventually _ char_bound he

private lemma twisted_approx {ε : ℝ} (he : 0 < ε) :
    ∃ T V : ℕ, 3 ≤ T ∧ 2 ≤ V ∧ ∀ᶠ X : ℕ in atTop,
      |primeMean (fun p => (chi p : ℝ)*scaledOff p) X -
       primeMean (fun p => (chi p : ℝ)*model T V p) X| ≤ ε := by
  obtain ⟨T,hT,H⟩ := ((eventually_ge_atTop 3).and (twisted_approx_eventually he)).exists
  obtain ⟨V,hV,h⟩ := ((eventually_ge_atTop 2).and H).exists
  exact ⟨T,V,hT,hV,h⟩

private lemma model_character_limit (hAP : ProgressionMangoldt) {T V : ℕ} (hT : 3 ≤ T) :
    ∃ L : ℝ, 4/15*commonWeight (2*V^52) 3 ≤ L ∧
      Tendsto (primeMean (fun p => (chi p : ℝ)*model T V p)) atTop (𝓝 L) := by
  let M := T.factorial
  let : NeZero M := ⟨(Nat.factorial_pos T).ne'⟩
  have hd (d : ℕ) (h : d ∈ Icc 2 T) (_ : Odd d) : d ∣ M :=
    Nat.dvd_factorial (by have := (mem_Icc.mp h).1; omega) (mem_Icc.mp h).2
  have hper : OnMod M (model T V) := low_onMod hd _ _
  have h3 : 3 ∣ M := Nat.dvd_factorial (by decide) hT
  refine ⟨_, twisted_low_lower hT hd (coneWindow (coneWidth V)) (by dsimp [coneWindow,coneWidth]; omega)
    (commonWeight (2*V^52)) (fun d _ => (commonWeight_bounds _ d).1), ?_⟩
  apply periodic_prime_mean hAP (q := M)
  intro n
  change (chi (n%M) : ℝ) * model T V (n%M) = (chi n : ℝ) * model T V n
  have hc : chi (n%M) = chi n := by simp only [chi,Nat.mod_mod_of_dvd _ h3]
  rw [hc,hper n]

/-- Arbitrarily close convergent models force an ordinary limit. -/
theorem limit_of_approximants {f : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → ℝ, ∃ L : ℝ,
      Tendsto g atTop (𝓝 L) ∧ ∀ᶠ X : ℕ in atTop, |f X-g X| ≤ ε) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hf : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε he
    obtain ⟨g,L,hg,H⟩ := h (ε/5) (by positivity)
    obtain ⟨n,hn⟩ := eventually_atTop.mp (H.and (Metric.tendsto_nhds.mp hg (ε/5) (by positivity)))
    refine ⟨n,fun i hi j hj => ?_⟩
    have ha := hn i hi
    have hb := hn j hj
    rw [Real.dist_eq] at ha hb ⊢
    apply abs_lt.mpr
    obtain ⟨ha₁,ha₂⟩ := abs_le.mp ha.1
    obtain ⟨hb₁,hb₂⟩ := abs_le.mp hb.1
    obtain ⟨ha₃,ha₄⟩ := abs_lt.mp ha.2
    obtain ⟨hb₃,hb₄⟩ := abs_lt.mp hb.2
    constructor <;> linarith
  exact cauchySeq_tendsto_of_complete hf

/-- Vanishing uniform mean approximation transfers existence of a limit and its lower bound. -/
theorem limit_of_prime_models {f : ℕ → ℝ} {b : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → ℝ, ∃ L : ℝ, b ≤ L ∧
      Tendsto g atTop (𝓝 L) ∧ ∀ᶠ X : ℕ in atTop, |f X - g X| ≤ ε) :
    ∃ L : ℝ, b ≤ L ∧ Tendsto f atTop (𝓝 L) := by
  obtain ⟨L,hL⟩ := limit_of_approximants (f:=f) (fun ε he => by
    obtain ⟨g,L,_,hg,H⟩ := h ε he
    exact ⟨g,L,hg,H⟩)
  refine ⟨L,?_,hL⟩
  by_contra! hbad
  let e := (b-L)/4
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨g,c,hc,hg,H⟩ := h e he
  obtain ⟨n,hn,hn',hn''⟩ := (H.and ((hg.eventually_const_lt (show c-e < c by linarith)).and
    (hL.eventually_lt_const (show L < L+e by linarith)))).exists
  have hd := (abs_le.mp hn).1
  dsimp only [e] at *
  linarith

/-- Existence and a quantitative lower bound for the complete off-diagonal
mean twisted by the real nonprincipal character modulo three. -/
theorem scaled_character_prime_mean (hAP : ProgressionMangoldt) {a : ℝ}
    (ha : ∀ V : ℕ, 2 ≤ V → a ≤ commonWeight (2*V^52) 3) :
    ∃ L : ℝ, 4/15*a ≤ L ∧ Tendsto (primeMean (fun p => (chi p : ℝ)*scaledOff p)) atTop (𝓝 L) := by
  apply limit_of_prime_models
  intro ε he
  obtain ⟨T,V,hT,hV,H⟩ := twisted_approx he
  obtain ⟨L,hL,hl⟩ := model_character_limit (V := V) hAP hT
  exact ⟨_,L,(mul_le_mul_of_nonneg_left (ha V hV) (by norm_num)).trans hL,hl,H⟩

#print axioms scaled_character_prime_mean

open ThetaPrimeDensity ThetaDiagonalConstant ThetaDivisibleDiagonal

/-- Second-order residual of the canonical integer sum at a prime denominator. -/
noncomputable def residual (p : ℕ) : ℝ := (S p : ℝ)/p - Real.log p/2

/-- Mean over the primes in one reduced class modulo three, normalized by
the number of primes in that class up to the endpoint. -/
noncomputable def classMean (r : ℕ) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ p ∈ primeSet (fun n => n%3=r) X, f p) / (primeSet (fun n => n%3=r) X).card

private lemma primeMean_linear (a b : ℝ) (f g : ℕ → ℝ) (X : ℕ) :
    primeMean (fun p => a*f p+b*g p) X = a*primeMean f X+b*primeMean g X := by
  simp only [primeMean,sum_add_distrib,← mul_sum]
  ring

/-- Eventual pointwise approximation along primes preserves the limiting prime mean. -/
theorem primeMean_of_close {f g : ℕ → ℝ} {L : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, p.Prime → |f p-g p| < ε)
    (hg : Tendsto (primeMean g) atTop (𝓝 L)) : Tendsto (primeMean f) atTop (𝓝 L) := by
  have hd : Tendsto (primeMean (fun p => f p-g p)) atTop (𝓝 0) :=
    prime_mean_of_convergence (by simpa only [sub_zero] using h)
  have H := hd.add hg
  rw [zero_add] at H
  apply H.congr'
  apply Eventually.of_forall
  intro X
  simp only [primeMean,sum_sub_distrib,sub_div,sub_add_cancel]

/-- The nonprincipal character modulo three has ordinary prime mean zero. -/
theorem chi_prime_mean (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun n => (chi n : ℝ))) atTop (𝓝 0) := by
  have hper : OnMod 3 (fun n => (chi n : ℝ)) := by intro n; simp [chi]
  have hz : unitMean 3 (fun n => (chi n : ℝ)) = 0 := by
    rw [unitMean,ThetaReciprocalFibers.unit_sum_nat (fun n => (chi n : ℝ)),sum_filter]
    norm_num [sum_range_succ,Nat.Coprime,chi]
  simpa only [hz] using periodic_prime_mean hAP hper

/-- A bounded weight transfers its own mean and its off-diagonal mean to the original residual. -/
theorem bounded_residual_mean {b L : ℝ} (w : ℕ → ℝ) (hw : ∀ p, |w p| ≤ 1)
    (hwb : Tendsto (primeMean w) atTop (𝓝 b))
    (hL : Tendsto (primeMean (fun p => w p*scaledOff p)) atTop (𝓝 L)) :
    Tendsto (primeMean (fun p => w p*residual p)) atTop (𝓝 (diagonalConstant*b+8/Real.pi^2*L)) := by
  let g (p : ℕ) := diagonalConstant*w p+(8/Real.pi^2)*(w p*scaledOff p)
  have hg := (hwb.const_mul diagonalConstant).add (hL.const_mul (8/Real.pi^2))
  apply primeMean_of_close (g := g) _ (hg.congr' (Eventually.of_forall (fun X =>
    (primeMean_linear diagonalConstant (8/Real.pi^2) (fun n => w n) (fun n => w n*scaledOff n) X).symm)))
  intro ε he
  filter_upwards [Metric.tendsto_nhds.mp diagonal_second_order ε he,eventually_gt_atTop 2] with p H hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
  have heq : w p*residual p - g p =
      w p*(divisibleDiagonal p/p-Real.log p/2-diagonalConstant) := by
    simp only [g,residual,scaledOff,S_eq_diagonal_add_offDiagonal hodd,add_div]
    field_simp [Real.pi_ne_zero]
    ring
  rw [heq,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hw p)).trans_lt H

/-- A centered bounded weight transfers an off-diagonal mean to the original residual. -/
theorem bounded_residual_twist {L : ℝ} (w : ℕ → ℝ) (hw : ∀ p, |w p| ≤ 1)
    (hw0 : Tendsto (primeMean w) atTop (𝓝 0))
    (hL : Tendsto (primeMean (fun p => w p*scaledOff p)) atTop (𝓝 L)) :
    Tendsto (primeMean (fun p => w p*residual p)) atTop (𝓝 (8/Real.pi^2*L)) := by
  simpa only [mul_zero,zero_add] using bounded_residual_mean w hw hw0 hL

/-- Convert a twisted off-diagonal mean to a mean of the original residual. -/
theorem residual_twist {L : ℝ} (hAP : ProgressionMangoldt)
    (hL : Tendsto (primeMean (fun p => (chi p : ℝ)*scaledOff p)) atTop (𝓝 L)) :
    Tendsto (primeMean (fun p => (chi p : ℝ)*residual p)) atTop (𝓝 (8/Real.pi^2*L)) :=
  bounded_residual_twist _ char_bound (chi_prime_mean hAP) hL

private lemma class_limit {r : ℕ} {s B C : ℝ} {f : ℕ → ℝ}
    (hrs : (r=1 ∧ s=1) ∨ (r=2 ∧ s= -1)) (hAP : ProgressionMangoldt)
    (hB : Tendsto (primeMean f) atTop (𝓝 B))
    (hC : Tendsto (primeMean (fun p => (chi p : ℝ)*f p)) atTop (𝓝 C)) :
    Tendsto (classMean r f) atTop (𝓝 (B+s*C)) := by
  let g (p : ℕ) := (1/2 : ℝ)*f p + (s/2)*((chi p : ℝ)*f p)
  have hg := (hB.const_mul (1/2 : ℝ)).add (hC.const_mul (s/2))
  have hsel : Tendsto (primeMean (fun p => if p%3=r then f p else 0))
      atTop (𝓝 ((1/2 : ℝ)*B+(s/2)*C)) := by
    apply primeMean_of_close (g := g) _ (hg.congr' (Eventually.of_forall (fun X =>
      (primeMean_linear (1/2) (s/2) f (fun n => (chi n : ℝ)*f n) X).symm)))
    intro ε he
    filter_upwards [eventually_gt_atTop 3] with p hp hprime
    have hn : ¬ 3 ∣ p := fun h => by
      rcases (Nat.dvd_prime hprime).mp h with h|h <;> omega
    have hmod : p%3=1 ∨ p%3=2 := by
      have := Nat.mod_lt p (by decide : 0 < 3)
      have := Nat.dvd_iff_mod_eq_zero.not.mp hn
      omega
    have heq : (if p%3=r then f p else 0) = g p := by
      rcases hrs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases hmod with h|h <;>
        norm_num [h,chi,g] <;> ring
    rw [heq,sub_self,abs_zero]; exact he
  have hc : r.Coprime 3 ∧ r < 3 := by rcases hrs with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
  have hd := class_prime_density hAP (q := 3) (by decide) hc.1 hc.2
  have ht : Nat.totient 3 = 2 := by decide
  rw [ht] at hd
  have H := hsel.div hd (by norm_num)
  have hlim : ((1/2 : ℝ)*B + s/2*C)/(1/(2:ℝ)) = B+s*C := by ring
  norm_num only [Nat.cast_ofNat] at H
  rw [hlim] at H
  apply H.congr'
  have hπ : Tendsto (fun N : ℕ => (N.primeCounting : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_gt_atTop 0] with X hx
  simp only [Pi.div_apply,primeMean,classMean,primeSet,sum_filter]
  field_simp
  congr 1
  apply sum_congr rfl
  intro p _
  by_cases h : p%3=r <;> simp [h]

/-- The ordinary second coefficients in the two prime progressions modulo
three differ by twice a strictly positive character mean. -/
theorem S_class_prime_means (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 968/(375*Real.pi^2) ≤ C ∧
      Tendsto (primeMean (fun p => (chi p : ℝ)*residual p)) atTop (𝓝 C) ∧
      Tendsto (classMean 1 residual) atTop (𝓝 (diagonalConstant+C)) ∧
      Tendsto (classMean 2 residual) atTop (𝓝 (diagonalConstant-C)) := by
  obtain ⟨L,hL,hl⟩ := scaled_character_prime_mean hAP (fun _ => ThetaHalfLogExcursions.common_factor_mass)
  let C := 8/Real.pi^2*L
  have hC := residual_twist hAP hl
  have hB : Tendsto (primeMean residual) atTop (𝓝 diagonalConstant) := S_second_order_prime_mean hAP
  refine ⟨C,?_,hC,?_,?_⟩
  · calc 968/(375*Real.pi^2) = (8/Real.pi^2)*(4/15*(121/100)) := by ring
         _ ≤ C := mul_le_mul_of_nonneg_left hL (by positivity)
  · simpa only [one_mul] using class_limit (Or.inl ⟨rfl,rfl⟩) hAP hB hC
  · simpa only [neg_one_mul,sub_eq_add_neg] using class_limit (Or.inr ⟨rfl,rfl⟩) hAP hB hC

#print axioms S_class_prime_means

/-- The two within-class means eventually lie on opposite sides of the
half-log term, with explicit strict margins. -/
theorem S_class_mean_signs (hAP : ProgressionMangoldt) :
    ∀ᶠ X : ℕ in atTop, 261/1000 < classMean 1 residual X ∧
      classMean 2 residual X < -(1/500) := by
  obtain ⟨C,hC,_,h₁,h₂⟩ := S_class_prime_means hAP
  have h : (261/1000 : ℝ) < 968/(375*Real.pi^2) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith only [mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4]
  have hpos := ThetaCenterBounds.center_bounds
  exact (h₁.eventually_const_lt (by linarith only [h,hC,hpos.1])).and
    (h₂.eventually_lt_const (by linarith only [h,hC,hpos.2]))

/-- The character correlation forces a quantitative lower bound on the
liminf of the centered second moment among all primes. -/
private lemma variance_from_character (hAP : ProgressionMangoldt) {C v : ℝ}
    (hχ : Tendsto (primeMean (fun p => (chi p : ℝ)*residual p)) atTop (𝓝 C)) (hv : v < C^2) : ∀ᶠ X : ℕ in atTop,
    v < primeMean (fun p => (residual p-diagonalConstant)^2) X := by
  let t := C
  let z (p : ℕ) := residual p-diagonalConstant
  have hcenter : Tendsto (primeMean (fun p => (chi p : ℝ)*z p)) atTop (𝓝 C) := by
    have H := hχ.add ((chi_prime_mean hAP).const_mul (-diagonalConstant))
    rw [mul_zero,add_zero] at H
    apply H.congr'
    apply Eventually.of_forall
    intro X
    change primeMean (fun p => (chi p : ℝ)*residual p) X +
      (-diagonalConstant)*primeMean (fun p => (chi p : ℝ)) X = _
    simp only [primeMean,← mul_div_assoc,← add_div,mul_sum,← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    dsimp only [z]
    ring
  have h1 : Tendsto (primeMean (fun _ => (1:ℝ))) atTop (𝓝 1) :=
    prime_mean_of_convergence (by intro ε he; simp [he])
  let g (p : ℕ) := 2*t*((chi p : ℝ)*z p)+(-t^2)*1
  have hg : Tendsto (primeMean g) atTop (𝓝 (2*t*C+(-t^2)*1)) :=
    ((hcenter.const_mul (2*t)).add (h1.const_mul (-t^2))).congr' (Eventually.of_forall
      (fun X => (primeMean_linear (2*t) (-t^2) (fun p => (chi p : ℝ)*z p) (fun _ => 1) X).symm))
  have hlim : v < 2*t*C+(-t^2)*1 := by dsimp [t]; linarith only [hv]
  filter_upwards [hg.eventually_const_lt hlim] with X hX
  apply hX.trans_le
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro p _
  dsimp only [g,z]
  unfold chi
  split_ifs <;> push_cast <;> nlinarith only [sq_nonneg (residual p-diagonalConstant-t),
    sq_nonneg (residual p-diagonalConstant+t),sq_nonneg (residual p-diagonalConstant),sq_nonneg t]

#print axioms S_class_mean_signs

private noncomputable def primeRms (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  Real.sqrt (primeMean (fun p => (f p)^2) X)

private lemma rms_sq (f : ℕ → ℝ) (X : ℕ) :
    (primeRms f X)^2 = primeMean (fun p => (f p)^2) X :=
  Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))

private lemma rms_triangle (f g : ℕ → ℝ) (X : ℕ) :
    primeRms (fun p => f p+g p) X ≤ primeRms f X + primeRms g X := by
  let P := Nat.primesLE X
  have hsq (h : ℕ → ℝ) : 0 ≤ ∑ p ∈ P, (h p)^2 := sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ∑ p ∈ P, (f p+g p)^2 =
      (∑ p ∈ P,(f p)^2) + 2*(∑ p ∈ P,f p*g p) + ∑ p ∈ P,(g p)^2 := by
    simp only [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    ring
  have hroot : Real.sqrt (∑ p ∈ P, (f p+g p)^2) ≤
      Real.sqrt (∑ p ∈ P,(f p)^2) + Real.sqrt (∑ p ∈ P,(g p)^2) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [hsum]
    nlinarith only [Real.sum_mul_le_sqrt_mul_sqrt P f g, Real.sq_sqrt (hsq f),Real.sq_sqrt (hsq g)]
  change Real.sqrt ((∑ p ∈ P,(f p+g p)^2)/X.primeCounting) ≤
    Real.sqrt ((∑ p ∈ P,(f p)^2)/X.primeCounting) + Real.sqrt ((∑ p ∈ P,(g p)^2)/X.primeCounting)
  rw [Real.sqrt_div (hsq (fun p => f p+g p)),Real.sqrt_div (hsq f),Real.sqrt_div (hsq g),← add_div]
  exact div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg _)

private lemma rms_dist (f g : ℕ → ℝ) (X : ℕ) :
    |primeRms f X - primeRms g X| ≤ primeRms (fun p => f p-g p) X := by
  have h₁ := rms_triangle g (fun p => f p-g p) X
  have h₂ := rms_triangle f (fun p => g p-f p) X
  simp only [add_sub_cancel] at h₁ h₂
  have he : primeRms (fun p => g p-f p) X = primeRms (fun p => f p-g p) X := by
    simp only [primeRms]
    congr 2
    funext p
    ring
  rw [he] at h₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

private lemma rms_mul (c : ℝ) (hc : 0 ≤ c) (f : ℕ → ℝ) (X : ℕ) :
    primeRms (fun p => c*f p) X = c*primeRms f X := by
  simp only [primeRms,primeMean,mul_pow,← mul_sum,mul_div_assoc,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]

private lemma rms_scaled_limit (hAP : ProgressionMangoldt) :
    ∃ K : ℝ, 0 ≤ K ∧ Tendsto (primeRms scaledOff) atTop (𝓝 K) := by
  apply limit_of_prime_models
  intro ε he
  obtain ⟨T,V,_,_,H⟩ := prime_model_approximation (sq_pos_of_pos he)
  let M := T.factorial
  let : NeZero M := ⟨(Nat.factorial_pos T).ne'⟩
  have hper : OnMod M (model T V) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  have hs : OnMod M (fun p => (model T V p)^2) := fun p => congrArg (·^2) (hper p)
  refine ⟨_,_,Real.sqrt_nonneg _,(periodic_prime_mean hAP hs).sqrt,?_⟩
  have hπ : Tendsto (fun N : ℕ => (N.primeCounting : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  filter_upwards [H,hπ.eventually_gt_atTop 0] with X hX hpos
  apply (rms_dist scaledOff (model T V) X).trans
  exact (Real.sqrt_le_left he.le).mpr ((div_le_iff₀ hpos).mpr hX)

/-- The remaining diagonal error vanishes in ordinary prime mean square. -/
theorem diagonal_square_error :
    Tendsto (primeMean (fun p => (residual p-diagonalConstant-8/Real.pi^2*scaledOff p)^2)) atTop (𝓝 0) := by
  have hd := ((diagonal_second_order.sub_const diagonalConstant).pow 2)
  rw [sub_self,show (0 : ℝ)^2=0 by norm_num] at hd
  apply prime_mean_of_convergence
  intro ε he
  filter_upwards [Metric.tendsto_nhds.mp hd ε he,eventually_gt_atTop 2] with p h hp hprime
  let : Fact p.Prime := ⟨hprime⟩
  have hh : residual p-diagonalConstant-8/Real.pi^2*scaledOff p = divisibleDiagonal p/p-Real.log p/2-diagonalConstant := by
    simp only [residual,scaledOff,S_eq_diagonal_add_offDiagonal (hprime.eq_two_or_odd.resolve_left (by omega)),add_div]
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [hh,Real.dist_eq] using h

#print axioms diagonal_square_error

/-- The centered second moment has a finite positive limit, with its
lower bound supplied by the modulo-three correlation. -/
private lemma variance_limit (hAP : ProgressionMangoldt) {C : ℝ}
    (hχ : Tendsto (primeMean (fun p => (chi p : ℝ)*residual p)) atTop (𝓝 C)) :
    ∃ V : ℝ, C^2 ≤ V ∧
      Tendsto (primeMean (fun p => (residual p-diagonalConstant)^2)) atTop (𝓝 V) := by
  let a := 8/Real.pi^2
  let f (p : ℕ) := residual p-diagonalConstant
  let g (p : ℕ) := a*scaledOff p
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have herr : Tendsto (primeRms (fun p => f p-g p)) atTop (𝓝 0) := by
    have hl : Tendsto (primeMean (fun p => (f p-g p)^2)) atTop (𝓝 0) := diagonal_square_error
    change Tendsto (fun X => Real.sqrt (primeMean (fun p => (f p-g p)^2) X)) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using hl.sqrt
  obtain ⟨K,_,hK⟩ := rms_scaled_limit hAP
  have hg : Tendsto (primeRms g) atTop (𝓝 (a*K)) :=
    (hK.const_mul a).congr' (Eventually.of_forall (fun X => (rms_mul a ha scaledOff X).symm))
  have hf : Tendsto (primeRms f) atTop (𝓝 (a*K)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [herr.eventually_lt_const (half_pos he), Metric.tendsto_nhds.mp hg (ε/2) (half_pos he)]
      with X hd hg'
    have hh := rms_dist f g X
    have htri := dist_triangle (primeRms f X) (primeRms g X) (a*K)
    rw [Real.dist_eq] at hg' ⊢
    simp only [Real.dist_eq] at htri
    linarith only [htri,hh,hd,hg']
  have hv := hf.pow 2
  simp only [rms_sq] at hv
  refine ⟨_,?_,hv⟩
  by_contra! h
  obtain ⟨v,h₁,h₂⟩ := exists_between h
  exact (not_frequently.mpr ((hv.eventually_lt_const h₁).mono (fun _ hx => hx.not_ge)))
    ((variance_from_character hAP hχ h₂).mono (fun _ hx => hx.le)).frequently

/-- Variance about the empirical mean of the same primes up to X. -/
noncomputable def sampleVariance (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  primeMean (fun p => (f p-primeMean f X)^2) X

theorem variance_recentering (f : ℕ → ℝ) (b : ℝ) {X : ℕ} (hx : 0 < (X.primeCounting : ℝ)) :
    sampleVariance f X = primeMean (fun p => (f p-b)^2) X - (primeMean f X-b)^2 := by
  have center (c : ℝ) : primeMean (fun p => (f p-c)^2) X =
      primeMean (fun p => (f p)^2) X - 2*c*primeMean f X + c^2 := by
    have he (p : ℕ) : (f p-c)^2 = (f p)^2-2*c*f p+c^2 := by ring
    simp only [primeMean,he,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,
      Nat.primesLE_card_eq_primeCounting]
    field_simp
  rw [sampleVariance,center,center]
  ring

/-- A single pair of constants controls both residue-class means and the
limiting variance, with either the fixed or the empirical center. -/
theorem S_prime_class_statistics (hAP : ProgressionMangoldt) :
    ∃ C V : ℝ, 968/(375*Real.pi^2) ≤ C ∧ C^2 ≤ V ∧
      Tendsto (classMean 1 residual) atTop (𝓝 (diagonalConstant+C)) ∧
      Tendsto (classMean 2 residual) atTop (𝓝 (diagonalConstant-C)) ∧
      Tendsto (primeMean (fun p => (residual p-diagonalConstant)^2)) atTop (𝓝 V) ∧
      Tendsto (sampleVariance residual) atTop (𝓝 V) := by
  obtain ⟨C,hC,hχ,h₁,h₂⟩ := S_class_prime_means hAP
  obtain ⟨V,hV,hlim⟩ := variance_limit hAP hχ
  refine ⟨C,V,hC,hV,h₁,h₂,hlim,?_⟩
  have hB : Tendsto (primeMean residual) atTop (𝓝 diagonalConstant) := S_second_order_prime_mean hAP
  have hh := hlim.sub ((hB.sub_const diagonalConstant).pow 2)
  rw [sub_self,show (0 : ℝ)^2=0 by norm_num,sub_zero] at hh
  apply hh.congr'
  have hπ : Tendsto (fun N : ℕ => (N.primeCounting : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_gt_atTop 0] with X hx
  exact (variance_recentering residual diagonalConstant hx).symm

#print axioms variance_recentering
#print axioms S_prime_class_statistics
#print axioms twisted_approx_eventually
#print axioms residual_twist
#print axioms chi_prime_mean

#print axioms bounded_twist_approx_eventually
#print axioms bounded_residual_twist
#print axioms primeMean_of_close
#print axioms limit_of_approximants
#print axioms limit_of_prime_models

end Arxiv.«2501.03234».ThetaCharacterPrimeMeans
