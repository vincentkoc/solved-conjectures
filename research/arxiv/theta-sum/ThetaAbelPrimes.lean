import ThetaConditionalRows
import Mathlib.Analysis.Normed.Group.Tannery
/-! Prime averages with a logarithmic weight and an Abel parameter. -/
namespace Arxiv.«2501.03234».ThetaAbelPrimes
open LSeries Finset Filter ArithmeticFunction ArithmeticFunction.vonMangoldt Complex

private lemma pole_identity {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {x : ℝ} (hx : 1<x) :
    (∑' n, residueClass a n/(n:ℝ)^x) = (LFunctionResidueClassAux a x).re+(q.totient:ℝ)⁻¹/(x-1) := by
  refine ofReal_injective ?_
  simp only [ofReal_tsum,ofReal_div,ofReal_cpow (Nat.cast_nonneg _),ofReal_natCast,
    ofReal_add,ofReal_inv,ofReal_sub,ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hx,eqOn_LFunctionResidueClassAux ha
    (Set.mem_ofPred.mpr (ofReal_re x ▸ hx)),sub_add_cancel,LSeries,term]
  refine tsum_congr (fun n => ?_)
  split_ifs with hn
  · simp only [hn,residueClass_apply_zero,ofReal_zero,zero_div]
  · rfl

noncomputable def parameter (k : ℕ) : ℝ := 1/((k:ℝ)+1)
private lemma parameter_pos (k) : 0<parameter k := by unfold parameter; positivity
private lemma parameter_le (k) : parameter k≤1 := by
  unfold parameter; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α:=ℝ) k]
private lemma parameter_limit : Tendsto parameter atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- Abel averages of the von Mangoldt weights are equidistributed on reduced classes. -/
theorem class_mangoldt {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun k => parameter k*∑' n,residueClass a n/(n:ℝ)^(1+parameter k)) atTop
      (nhds (q.totient:ℝ)⁻¹) := by
  have hc : ContinuousOn (fun x : ℝ => (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t:=Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun _ _ => trivial) |>.comp continuous_ofReal.continuousOn (fun x hx => by
        simpa only [Set.mem_ofPred_eq,ofReal_re] using hx.1)
  have ht : Tendsto (fun k => 1+parameter k) atTop (nhds (1:ℝ)) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).add parameter_limit
  have hmem : ∀ᶠ k in atTop,1+parameter k∈Set.Icc (1:ℝ) 2 := Eventually.of_forall
    (fun k => ⟨by linarith [parameter_pos k],by linarith [parameter_le k]⟩)
  have hlim := (hc 1 (show (1:ℝ)∈Set.Icc 1 2 by norm_num)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨ht,hmem⟩)
  have H := (parameter_limit.mul hlim).add_const (q.totient:ℝ)⁻¹
  simp only [zero_mul,zero_add] at H
  apply H.congr'; filter_upwards with k
  rw [pole_identity ha (by linarith [parameter_pos k]),add_sub_cancel_left,mul_add]
  field_simp [(parameter_pos k).ne']
  rfl

private noncomputable def correction {q : ℕ} (a : ZMod q) (x : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 0 else residueClass a n)/(n:ℝ)^x

private lemma correction_nonneg {q : ℕ} (a : ZMod q) (x : ℝ) (n : ℕ) :
    0≤correction a x n := by
  unfold correction
  positivity [residueClass_nonneg a n]

private lemma correction_le {q : ℕ} (a : ZMod q) {x : ℝ} (hx : 1≤x) (n : ℕ) :
    correction a x n ≤ (if n.Prime then 0 else residueClass a n)/n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [correction]
  · apply div_le_div_of_nonneg_left (by positivity [residueClass_nonneg a n]) (by exact_mod_cast hn)
    conv_lhs => rw [← Real.rpow_one n]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx

/-- The logarithmically weighted prime mass in a reduced residue class tends
to the reciprocal of the totient as the exponent decreases to one. -/
theorem class_primes {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun k => parameter k*∑' n : ℕ,
      (if n.Prime ∧ (n:ZMod q)=a then Real.log n else 0)/(n:ℝ)^(1+parameter k)) atTop
      (nhds (q.totient:ℝ)⁻¹) := by
  let C := ∑' n : ℕ,(if n.Prime then 0 else residueClass a n)/n
  have ha' := summable_residueClass_non_primes_div a
  have hs (k) : Summable (correction a (1+parameter k)) :=
    Summable.of_nonneg_of_le (correction_nonneg a (1+parameter k)) (correction_le a (by linarith [parameter_pos k])) ha'
  have H : Tendsto (fun k => parameter k*∑' n,correction a (1+parameter k) n) atTop (nhds 0) := by
    have hl := parameter_limit.mul_const C
    rw [zero_mul] at hl
    apply squeeze_zero (fun k => mul_nonneg (parameter_pos k).le (tsum_nonneg (correction_nonneg a (1+parameter k))))
      (fun k => mul_le_mul_of_nonneg_left ((hs k).tsum_le_tsum (correction_le a
        (by linarith [parameter_pos k])) ha') (parameter_pos k).le) hl
  have h := (class_mangoldt ha).sub H
  rw [sub_zero] at h
  apply h.congr'; filter_upwards with k
  rw [← mul_sub]
  congr 1
  have hfull : Summable (fun n : ℕ => residueClass a n/(n:ℝ)^(1+parameter k)) :=
    summable_real_of_abscissaOfAbsConv_lt <| (abscissaOfAbsConv_residueClass_le_one a).trans_lt <|
      mod_cast (show (1:ℝ)<1+parameter k by linarith [parameter_pos k])
  rw [← hfull.tsum_sub (hs k)]
  apply tsum_congr; intro n
  by_cases hp : n.Prime
  · simp [correction,hp,residueClass,Set.indicator, vonMangoldt_apply_prime hp]
  · simp [correction,hp]

open ThetaConditionalRows ThetaPeriodMeans ThetaRowCorrelations ThetaCharacterThree

private noncomputable def atom {q : ℕ} (a : ZMod q) (k n : ℕ) : ℝ :=
  (if n.Prime ∧ (n:ZMod q)=a then Real.log n else 0)/(n:ℝ)^(1+parameter k)

private lemma atom_summable {q : ℕ} (a : ZMod q) (k : ℕ) : Summable (atom a k) := by
  have hs : Summable (fun n : ℕ => residueClass a n/(n:ℝ)^(1+parameter k)) :=
    summable_real_of_abscissaOfAbsConv_lt <| (abscissaOfAbsConv_residueClass_le_one a).trans_lt <|
      mod_cast (show (1:ℝ)<1+parameter k by linarith [parameter_pos k])
  apply Summable.of_nonneg_of_le _ _ hs
  · intro n; unfold atom; split_ifs with h
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.1.one_le)) (by positivity)
    · simp
  · intro n; apply div_le_div_of_nonneg_right _ (by positivity)
    split_ifs with h
    · simp [residueClass,Set.indicator,h.2,vonMangoldt_apply_prime h.1]
    · exact residueClass_nonneg a n

/-- The Abel-weighted sum runs over primes coprime to the fixed period.
The omitted primes divide that period. -/
noncomputable def primeAverage (q : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  parameter k*∑' n : ℕ,
    (if n.Prime ∧ n.Coprime q then f n * Real.log n else 0)/(n:ℝ)^(1+parameter k)

/-- A periodic test has limiting Abel prime average equal to its normalized
mean over reduced residues. -/
theorem periodic_prime_limit {q : ℕ} [NeZero q] {f : ℕ → ℝ} (hf : OnMod q f) :
    Tendsto (primeAverage q f) atTop (nhds (unitMean q f)) := by
  classical
  let F (u : (ZMod q)ˣ) := f (u:ZMod q).val
  have H (u : (ZMod q)ˣ) : Tendsto (fun k => F u*(parameter k*∑' n,atom (u:ZMod q) k n)) atTop
        (nhds (F u*(q.totient:ℝ)⁻¹)) := (class_primes u.isUnit).const_mul (F u)
  have hl := tendsto_finsetSum univ (fun u _ => H u)
  change Tendsto (fun k => ∑ u : (ZMod q)ˣ,F u*(parameter k*∑' n,atom (u:ZMod q) k n)) atTop
    (nhds (∑ u : (ZMod q)ˣ,F u*(q.totient:ℝ)⁻¹)) at hl
  rw [← sum_mul,← div_eq_mul_inv] at hl
  apply hl.congr'; filter_upwards with k
  have hs (u : (ZMod q)ˣ) : Summable (fun n => F u*atom (u:ZMod q) k n) :=
    (atom_summable _ k).mul_left _
  have he (n : ℕ) : (∑ u : (ZMod q)ˣ,F u*atom (u:ZMod q) k n) =
      (if n.Prime ∧ n.Coprime q then f n*Real.log n else 0)/(n:ℝ)^(1+parameter k) := by
    by_cases hn : n.Prime
    · by_cases hc : n.Coprime q
      · let v := ZMod.unitOfCoprime n hc
        have eqv (u : (ZMod q)ˣ) : ((n:ZMod q)=(u:ZMod q)) ↔ v=u := by
          change ((v:ZMod q)=(u:ZMod q)) ↔ v=u
          exact ⟨Units.ext,fun H => congrArg Units.val H⟩
        have hv : F v=f n := by simp only [F,v,ZMod.coe_unitOfCoprime,ZMod.val_natCast,hf n]
        rw [if_pos ⟨hn,hc⟩]
        simp only [atom,hn,true_and,eqv,mul_div_assoc',mul_ite,mul_zero,← sum_div,
          sum_ite_eq,mem_univ,ite_true,hv]
      · have hnu (u : (ZMod q)ˣ) : (n:ZMod q)≠(u:ZMod q) := fun H =>
          hc ((ZMod.isUnit_iff_coprime n q).mp (H ▸ u.isUnit))
        simp [atom,hnu,hc]
    · simp [atom,hn]
  calc
    _ = parameter k*∑ u : (ZMod q)ˣ,F u*∑' n,atom (u:ZMod q) k n := by
      rw [mul_sum]; apply sum_congr rfl; intro u _; ring
    _ = parameter k*∑' n,∑ u : (ZMod q)ˣ,F u*atom (u:ZMod q) k n := by
      rw [Summable.tsum_finsetSum (fun u _ => hs u)]
      simp only [tsum_mul_left]
    _ = _ := congrArg (parameter k*·) (tsum_congr he)

open ThetaReciprocalBlocks ThetaReciprocalInversion ThetaNondivisibleCone

/-- For each entire fixed rational cone, the two restricted Abel prime
averages converge to opposite signed limits, uniformly separated from zero.
Here M is any odd common period of the odd denominators through 2J. -/
theorem rationalCone_prime_bias {J K M : ℕ} [NeZero M] (hM : Odd M) (hJ : 2≤J)
    (hK : K%2=1) (hdM : ∀ d∈Icc 2 (2*J), Odd d → d∣M) :
    ∃ b₁ b₁₇ : ℝ, 1/30≤b₁ ∧ b₁₇≤ -(1/30) ∧
      Tendsto (primeAverage (8*M) (fun p => if p%24=1 then (rationalCone p J K:ℝ) else 0))
        atTop (nhds b₁) ∧
      Tendsto (primeAverage (8*M) (fun p => if p%24=17 then (rationalCone p J K:ℝ) else 0))
        atTop (nhds b₁₇) := by
  let L := low (2*J) (coneWindow K) (commonWeight (2*J))
  have hT : 3≤2*J := by omega
  have hw : 0<coneWindow K 3 := by simp [coneWindow]; omega
  have h3 := hdM 3 (mem_Icc.mpr ⟨by decide,hT⟩) (by decide)
  have h24 : 24∣8*M := Nat.mul_dvd_mul_left 8 h3
  have hL : OnMod (8*M) L := onMod_lift (Nat.dvd_mul_left M 8) (low_onMod hdM _ _)
  have hp' (p : ℕ) (hp : p.Prime) (hc : p.Coprime (8*M)) : 2*J<p := by
    by_contra! h
    have hn := hp.coprime_iff_not_dvd.mp hc
    rcases hp.eq_two_or_odd with rfl|ho
    · exact hn (dvd_mul_of_dvd_left (by decide : 2∣8) _)
    · exact hn ((hdM p (mem_Icc.mpr ⟨hp.two_le,h⟩) (Nat.odd_iff.mpr ho)).trans (Nat.dvd_mul_left M 8))
  let F (r n : ℕ) := if n%24=r then L n else 0
  have hf (r : ℕ) : OnMod (8*M) (F r) := by
    intro n; dsimp only [F]; rw [Nat.mod_mod_of_dvd n h24,hL n]
  have hb (r : ℕ) : Tendsto (primeAverage (8*M) (fun p => if p%24=r then (rationalCone p J K:ℝ) else 0))
      atTop (nhds (unitMean (8*M) (F r))) := by
    apply (periodic_prime_limit (hf r)).congr'; filter_upwards with k
    unfold primeAverage; congr 1; apply tsum_congr; intro p
    by_cases H : p.Prime ∧ p.Coprime (8*M)
    · simp only [if_pos H,F,L,cone_eq_low H.1 (hp' p H.1 H.2) hK]
    · simp only [if_neg H]
  have hs := low_class_bias hM hT hdM (coneWindow K) hw (commonWeight (2*J))
    (fun d _ => (commonWeight_bounds _ d).1)
  have hl : (1:ℝ)/30≤commonWeight (2*J) 3/30 :=
    div_le_div_of_nonneg_right (commonWeight_three hT) (by norm_num)
  exact ⟨_,_,hl.trans hs.1,hs.2.trans (neg_le_neg hl),hb 1,hb 17⟩

end Arxiv.«2501.03234».ThetaAbelPrimes
#print axioms Arxiv.«2501.03234».ThetaAbelPrimes.rationalCone_prime_bias
#print axioms Arxiv.«2501.03234».ThetaAbelPrimes.class_mangoldt
#print axioms Arxiv.«2501.03234».ThetaAbelPrimes.periodic_prime_limit
#print axioms Arxiv.«2501.03234».ThetaAbelPrimes.class_primes
