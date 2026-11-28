import ThetaModelPeriods

/-! Character correlations and approximation errors inside a reduced dyadic progression. -/
namespace Arxiv.«2501.03234».ThetaDyadicSpectrum
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaPrimeDensity ThetaCharacterPrimeMeans ThetaDyadicLaw ThetaPeriodMeans ThetaDirichletRows

noncomputable def progressionMeanC (D a : ℕ) (f : ℕ → ℂ) (X : ℕ) : ℂ :=
  let s := primeSet (fun p => p%D=a) X
  (∑ p∈s,f p)/(s.card:ℂ)

private theorem parts {q : ℕ} (χ : DirichletCharacter ℂ q) (D a : ℕ) (f : ℕ → ℝ) (X : ℕ) :
    (progressionMeanC D a (fun p => symbol χ p*(f p:ℂ)) X).re =
      progressionMean D a (fun p => (symbol χ p).re*f p) X ∧
    (progressionMeanC D a (fun p => symbol χ p*(f p:ℂ)) X).im =
      progressionMean D a (fun p => (symbol χ p).im*f p) X := by
  simp [progressionMeanC,progressionMean,mul_re,mul_im,mul_comm]

/-- On a fixed reduced dyadic class, every odd-conductor primitive character has the
same correlation with the original residual as on all primes. -/
theorem class_correlation {k a q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (ho : _root_.Odd q) (hq : 1<q) (ha : a.Coprime (2^k)) (hlt : a<2^k)
    (hAP : ProgressionMangoldt) :
    Tendsto (progressionMeanC (2^k) a (fun p => symbol χ p*(residual p:ℂ))) atTop (𝓝 (coefficient χ)) := by
  have H := prime_correlation χ hχ ho hq hAP
  have PS : OnMod q (symbol χ) := fun n => by simp [symbol,ZMod.natCast_mod]
  apply complex_limit
  · simp only [(parts χ _ _ _ _).1]
    apply dyadic_restriction hAP ha hlt ho (fun n => congrArg re (PS n)) LipschitzWith.id
    simpa only [id_eq,ThetaCharacterPrimeMeans.residual,(components χ _ _).1,Function.comp_def] using
      (continuous_re.continuousAt.tendsto.comp H)
  · simp only [(parts χ _ _ _ _).2]
    apply dyadic_restriction hAP ha hlt ho (fun n => congrArg im (PS n)) LipschitzWith.id
    simpa only [id_eq,ThetaCharacterPrimeMeans.residual,(components χ _ _).2,Function.comp_def] using
      (continuous_im.continuousAt.tendsto.comp H)

private theorem class_blind {D a q m : ℕ} [NeZero D] [NeZero q] [NeZero m]
    (χ : DirichletCharacter ℂ q) (hm : ¬χ.conductor∣D*m)
    (ha : a.Coprime D) (hlt : a<D) (hAP : ProgressionMangoldt) {g : ℕ → ℝ} (hg : OnMod m g) :
    Tendsto (progressionMeanC D a (fun p => symbol χ p*(g p:ℂ))) atTop (𝓝 0) := by
  let v (n : ℕ) : ℝ := if n%D=a then g n else 0
  have hv : OnMod (D*m) v := by
    intro n
    have he := onMod_lift (Nat.dvd_mul_right D m) (f:=fun t : ℕ => t%D)
      (fun t => Nat.mod_mod t D) n
    simp only [v,he,onMod_lift (Nat.dvd_mul_left m D) hg n]
  have H := blind_limit χ hm hAP hv
  have den := class_prime_density hAP (NeZero.pos D) ha hlt
  have hz : (1/(D.totient:ℂ))≠0 := one_div_ne_zero (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos D)).ne')
  have hden : Tendsto (fun X : ℕ => ((primeSet (fun n => n%D=a) X).card:ℂ)/X.primeCounting) atTop
      (𝓝 (1/(D.totient:ℂ))) := by
    simpa only [Function.comp_def,ofReal_div,ofReal_one,ofReal_natCast] using
      (continuous_ofReal.continuousAt.tendsto.comp den)
  have ht := H.div hden hz
  rw [zero_div] at ht
  apply ht.congr'
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_ne_atTop 0] with X hX
  have hx : (X.primeCounting:ℂ) ≠ 0 := by exact_mod_cast (by exact_mod_cast (show (X.primeCounting:ℝ)≠0 from hX) : X.primeCounting≠0)
  change (∑ p∈Nat.primesLE X,symbol χ p*(v p:ℂ))/(X.primeCounting:ℂ)/_ = _
  have Hs : (∑ p∈Nat.primesLE X,symbol χ p*(v p:ℂ))=
      ∑ p∈primeSet (fun n => n%D=a) X,symbol χ p*(g p:ℂ) := by
    rw [primeSet,sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hh : p%D=a <;> simp [v,hh]
  rw [Hs,progressionMeanC]
  dsimp only
  field_simp

theorem class_gap {k a q m : ℕ} [NeZero q] [NeZero m] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (ho : _root_.Odd q) (hq : 1<q) (hm : ¬q∣m)
    (ha : a.Coprime (2^k)) (hlt : a<2^k) (hAP : ProgressionMangoldt)
    {g : ℕ → ℝ} (hg : OnMod m g) {c : ℝ} (hc : c<‖coefficient χ‖) :
    ∀ᶠ X in atTop,c<progressionMean (2^k) a (fun p => |residual p-g p|) X := by
  have hmiss : ¬χ.conductor∣(2^k)*m := by
    rw [show χ.conductor=q from hχ]
    exact fun h => hm ((ho.coprime_two_right.pow_right k).dvd_mul_left.mp h)
  have H := (class_correlation χ hχ ho hq ha hlt hAP).sub (class_blind χ hmiss ha hlt hAP hg)
  rw [sub_zero] at H
  filter_upwards [H.norm (eventually_gt_nhds hc)] with X hX
  apply hX.trans_le
  change ‖progressionMeanC _ _ _ X-progressionMeanC _ _ _ X‖ ≤ _
  simp only [progressionMeanC,←sub_div,←sum_sub_distrib,←mul_sub,←ofReal_sub,norm_div,norm_natCast,progressionMean]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro p _
  rw [norm_mul,norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)

private theorem class_upper {D a : ℕ} [NeZero D] (ha : a.Coprime D) (hlt : a<D)
    (hAP : ProgressionMangoldt) {ε : ℝ} (he : 0<ε) {f : ℕ → ℝ} (hf : ∀ p,0≤f p)
    (H : ∀ᶠ X in atTop, primeMean f X ≤ ε*(1/(D.totient:ℝ))/2) :
    ∀ᶠ X in atTop, progressionMean D a f X ≤ ε := by
  let c : ℝ := 1/(D.totient:ℝ)
  have hc : 0<c := one_div_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos D))
  have hd := class_prime_density hAP (NeZero.pos D) ha hlt
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [H,hd.eventually_const_lt (half_lt_self hc),hπ.eventually_gt_atTop 0] with X hM hD hX
  let s := primeSet (fun n => n%D=a) X
  change 0<(X.primeCounting:ℝ) at hX
  have hden : c/2*(X.primeCounting:ℝ)<s.card := (lt_div_iff₀ hX).mp hD
  have hpos : 0<(s.card:ℝ) := (mul_pos (half_pos hc) hX).trans hden
  have hsub : s⊆Nat.primesLE X := by
    intro p hp
    simp only [s,primeSet,mem_filter] at hp
    exact hp.1
  have hs := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)
  change (∑ p∈Nat.primesLE X,f p)/(X.primeCounting:ℝ) ≤ ε*c/2 at hM
  change (∑ p∈s,f p)/(s.card:ℝ) ≤ ε
  apply (div_le_iff₀ hpos).mpr
  exact hs.trans (((div_le_iff₀ hX).mp hM).trans (by nlinarith only [mul_le_mul_of_nonneg_left hden.le he.le]))

/-- Exactly the same periods suffice in each reduced dyadic class, including one modulo eight.
The error is normalized by the count of primes in that class. -/
theorem fixed_class_models_iff {m : ℕ → ℕ} (hm : ∀ j, 0 < m j) {k a : ℕ}
    (ha : a.Coprime (2^k)) (hlt : a<2^k) (hAP : ProgressionMangoldt) :
    (∃ g : ℕ → ℕ → ℝ, (∀ j, OnMod (m j) (g j)) ∧ ∀ ε : ℝ, 0<ε →
      ∀ᶠ j in atTop, ∀ᶠ X in atTop, progressionMean (2^k) a (fun p => |residual p-g j p|) X ≤ ε) ↔
    ∀ q : ℕ, _root_.Odd q → ∀ᶠ j in atTop, q∣m j := by
  constructor
  · rintro ⟨g,hg,H⟩
    apply ThetaModelPeriods.odd_moduli_of_powers
    intro p hp ho b
    obtain ⟨χ,hχ,hodd⟩ := ThetaPrimePowerDigit.exists_primitive_odd hp ho b
    let : NeZero (p^(b+1)) := ⟨(pow_pos hp.pos _).ne'⟩
    have hpo := (hp.odd_of_ne_two ho).pow (n:=b+1)
    have hq := one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero b)
    have hn := (spectrum χ hχ hq hAP).2.mpr ⟨hpo,hodd⟩
    rw [if_pos hpo] at hn
    have hnorm := norm_pos_iff.mpr hn
    filter_upwards [H _ (half_pos hnorm)] with j hj
    by_contra hmiss
    let : NeZero (m j) := ⟨(hm j).ne'⟩
    have hG := class_gap χ hχ hpo hq hmiss ha hlt hAP (hg j) (half_lt_self hnorm)
    exact (hj.and hG).exists.elim fun _ hX => hX.2.not_ge hX.1
  · intro h
    obtain ⟨g,hg,H⟩ := (ThetaModelPeriods.fixed_models_iff hm hAP).mpr h
    refine ⟨g,hg,?_⟩
    intro ε he
    let D := 2^k
    have hd : 0<((D.totient):ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by dsimp [D]; positivity)
    filter_upwards [H (ε*(1/(D.totient:ℝ))/2) (by positivity)] with j hj
    exact class_upper ha hlt hAP he (fun p => abs_nonneg _) hj

theorem one_mod_eight_squarefree_gap {m : ℕ} [NeZero m] (hm : Squarefree m)
    (hAP : ProgressionMangoldt) {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X in atTop, 1/32<progressionMean 8 1 (fun p => |(S p:ℝ)/p-Real.log p/2-g p|) X := by
  apply class_gap (k:=3) ThetaSexticNine.chi ThetaSexticNine.chi_primitive (by decide) (by decide)
    _ (by decide) (by decide) hAP hg nine_bound
  intro h
  exact (by decide : ¬IsUnit (3:ℕ)) (hm 3 h)

#print axioms fixed_class_models_iff
#print axioms one_mod_eight_squarefree_gap

#print axioms class_correlation
#print axioms class_gap
end Arxiv.«2501.03234».ThetaDyadicSpectrum
