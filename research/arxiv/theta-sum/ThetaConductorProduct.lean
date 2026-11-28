import ThetaQuotientGap
import Mathlib.NumberTheory.EulerProduct.Basic

/-! Euler factors of the quadratic conductor correlation. -/
namespace Arxiv.«2501.03234».ThetaConductorProduct
open Finset Filter Topology ThetaLegendreFactors ThetaPrimeSpectrum
variable (q : ℕ) [Fact q.Prime]

private noncomputable abbrev ch (n : ℕ) : ℝ := (symbol q n:ℝ)

private noncomputable def localWeight (p : ℕ) : ℝ := (1-ch q p)*(1-ch q p/p)

noncomputable def weight (d : ℕ) : ℝ :=
  if Odd d then (∏ p∈d.primeFactors,localWeight q p)/((d:ℝ)*d.totient) else 0

private lemma weight_zero : weight q 0=0 := by simp [weight]
private lemma weight_one : weight q 1=1 := by simp [weight]

theorem weight_mul {a b : ℕ} (hc : a.Coprime b) : weight q (a*b)=weight q a*weight q b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b
  · have ha0 : a≠0 := fun h => by simp [h] at ha
    have hb0 : b≠0 := fun h => by simp [h] at hb
    simp only [weight,if_pos ha,if_pos hb,if_pos (ha.mul hb),Nat.primeFactors_mul ha0 hb0,
      prod_union hc.disjoint_primeFactors,Nat.totient_mul hc,Nat.cast_mul]
    ring
  all_goals simp [weight,Nat.odd_mul,ha,hb]

private lemma local_conductor : localWeight q q=1 := by simp [localWeight,ch,symbol_zero q (dvd_refl q)]

/-- The row amplitude is a constant times an ordinary multiplicative weight
restricted to the multiples of the conductor. -/
theorem amplitude_eq (d : ℕ) : amplitude q d =
    if q∣d then (1-ch q 2/2)*weight q d else 0 := by
  by_cases ho : Odd d <;> by_cases hd : q∣d
  · have h2 : 2 ∉ d.primeFactors := fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors h))
    have h2' : 2 ∉ d.primeFactors.erase q := fun h => h2 ((mem_erase.mp h).2)
    have hq : q∈d.primeFactors := Nat.mem_primeFactors.mpr ⟨Fact.out,hd,fun h => by simp [h] at ho⟩
    have he : (∏ p∈d.primeFactors,localWeight q p) = ∏ p∈d.primeFactors.erase q,localWeight q p := by
      rw [← mul_prod_erase _ _ hq,local_conductor,one_mul]
    simp only [amplitude,if_pos (show Odd d ∧ q∣d from ⟨ho,hd⟩),if_pos hd,weight,if_pos ho,prod_insert h2',he]
    change (∏ p∈d.primeFactors.erase q,(1-ch q p))*((1-ch q 2/2)*∏ p∈d.primeFactors.erase q,(1-ch q p/p))/_ = _
    simp only [localWeight,prod_mul_distrib]
    ring
  all_goals simp [amplitude,weight,ho,hd]

private theorem prime_power (p : ℕ) (hp : p.Prime) (n : ℕ) :
    weight q (p^(n+1)) = weight q p*(1/(p:ℝ)^2)^n := by
  by_cases ho : Odd p
  · have he : Odd (p^(n+1)) := ho.pow
    simp only [weight,if_pos ho,if_pos he,Nat.primeFactors_prime_pow (Nat.succ_ne_zero n) hp,
      hp.primeFactors,prod_singleton,Nat.totient_prime_pow_succ hp,Nat.totient_prime hp,
      Nat.cast_mul,Nat.cast_pow,pow_succ (p:ℝ) n,one_div,inv_pow,← pow_mul]
    ring
  · have h2 := hp.eq_two_or_odd.resolve_right (fun h => ho (Nat.odd_iff.mpr h))
    subst p
    simp [weight,Nat.odd_pow_iff,ho]

private theorem local_series (p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => weight q (p^e)) (1+weight q p/(1-1/(p:ℝ)^2)) := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hsq : (1:ℝ)<(p:ℝ)^2 := by nlinarith
  have hn : ‖1/(p:ℝ)^2‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_lt_one (by positivity)).mpr hsq
  have h := (hasSum_geometric_of_norm_lt_one hn).mul_left (weight q p)
  rw [← hasSum_nat_add_iff' 1]
  simp only [sum_range_one,pow_zero,weight_one,prime_power q p hp]
  simpa only [div_eq_mul_inv,add_sub_cancel_left] using h

/-- Local Euler series for the odd squarefree support away from the conductor. -/
noncomputable def inertFactor (p : ℕ) : ℝ :=
  if Odd p ∧ symbol q p = -1 then 1+2/((p:ℝ)-1)^2 else 1

theorem prime_factor (p : ℕ) (hp : p.Prime) (hq : q≠2) :
    ∑' e : ℕ, weight q (p^e) =
      if p=q then 1+(q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)) else inertFactor q p := by
  rw [(local_series q p hp).tsum_eq]
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 := zero_lt_one.trans hp1
  have hpow : (p:ℝ)^2-1≠0 := by nlinarith
  have hpm := sub_ne_zero.mpr hp1.ne'
  by_cases h2 : p=2
  · subst p
    have he : ¬ Odd 2 := by decide
    simp [hq.symm,weight,inertFactor,he]
  have ho : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left h2)
  simp only [weight,if_pos ho,hp.primeFactors,prod_singleton,Nat.totient_prime hp,
    Nat.cast_sub hp.one_le,Nat.cast_one]
  by_cases h : p=q
  · subst p
    rw [if_pos rfl,local_conductor]
    field_simp
  · rw [if_neg h]
    have hn : ¬q∣p := fun H => h ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hp).mp H).symm
    rcases symbol_unit q hn with he|he
    · simp [inertFactor,ho,he,localWeight,ch]
    · simp [inertFactor,ho,he,localWeight,ch]
      field_simp
      ring

private lemma ch_le_one (n : ℕ) : ch q n ≤ 1 := by
  by_cases h : q∣n
  · simp [ch,symbol_zero q h]
  · rcases symbol_unit q h with h|h <;> norm_num [ch,h]

private lemma multiplier_pos : 0<1-ch q 2/2 := by linarith [ch_le_one q 2]

private lemma weight_nonneg (n : ℕ) : 0 ≤ weight q n := by
  unfold weight
  split_ifs
  · apply div_nonneg _ (by positivity)
    apply prod_nonneg
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp'.one_le
    apply mul_nonneg (sub_nonneg.mpr (ch_le_one q p)) (sub_nonneg.mpr ?_)
    rw [div_le_iff₀ (by positivity : 0<(p:ℝ)),one_mul]
    exact (ch_le_one q p).trans hp1
  · exact le_rfl

/-- Absolute summability and the value of the row-amplitude series follow from
the ordered transfer because every row amplitude is nonnegative. -/
theorem amplitude_sum (hAP : ThetaNaturalPrimeMeans.ProgressionMangoldt) (hq : q%4=3) :
    ∃ L C : ℝ, 0<L ∧
      Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L) ∧
      Tendsto (ThetaNaturalPrimeMeans.primeMean
        (fun p => (symbol q p:ℝ)*ThetaCharacterPrimeMeans.residual p)) atTop (𝓝 C) ∧
      HasSum (amplitude q) (C/((parityFactor q:ℝ)*L)) := by
  obtain ⟨L,C,hl,hL,hC,_,_,_,hlim⟩ := prime_correlation q hAP hq
  refine ⟨L,C,hl,hL,hC,(hasSum_iff_tendsto_nat_of_nonneg (amplitude_nonneg q) _).mpr ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).1
  have hn : (parityFactor q:ℝ)*L ≠ 0 :=
    mul_ne_zero (by exact_mod_cast parityFactor_nonzero q hq) hl.ne'
  apply (hlim.div_const ((parityFactor q:ℝ)*L)).congr'
  filter_upwards with N
  rw [mul_div_cancel_left₀ _ hn]
  apply sum_subset
  · intro d hd
    exact mem_range.mpr (by have := (mem_Icc.mp hd).2; omega)
  · intro d hd hneg
    have h1 : d<2 := by
      have := mem_range.mp hd
      by_contra! h
      exact hneg (mem_Icc.mpr ⟨h,by omega⟩)
    interval_cases d <;> simp [amplitude,(Fact.out : q.Prime).not_dvd_one]

private lemma conductor_weight_pos (hq : q≠2) : 0 < weight q q := by
  have hp := (Fact.out : q.Prime)
  have ho := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hq)
  rw [weight,if_pos ho,hp.primeFactors,prod_singleton,local_conductor]
  have hq0 := hp.pos
  have ht := Nat.totient_pos.mpr hp.pos
  positivity

private theorem weight_summable (hq : q≠2) (hs : Summable (amplitude q)) : Summable (weight q) := by
  let K := 1-ch q 2/2
  have hk : 0<K := multiplier_pos q
  have hw := conductor_weight_pos q hq
  have hq0 := (Fact.out : q.Prime).ne_zero
  have H := (hs.div_const K).add
    ((hs.comp_injective (mul_right_injective₀ hq0)).div_const (K*weight q q))
  apply Summable.of_nonneg_of_le (weight_nonneg q) _ H
  intro n
  change weight q n ≤ amplitude q n/K + amplitude q (q*n)/(K*weight q q)
  by_cases hd : q∣n
  · rw [amplitude_eq q n,if_pos hd]
    change weight q n ≤ K*weight q n/K + _
    rw [mul_div_cancel_left₀ _ hk.ne']
    exact le_add_of_nonneg_right (div_nonneg (amplitude_nonneg q _) (mul_pos hk hw).le)
  · have hc := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr hd
    rw [amplitude_eq q n,if_neg hd,zero_div,zero_add,amplitude_eq q (q*n),
      if_pos (Nat.dvd_mul_right q n),weight_mul q hc]
    change weight q n ≤ K*(weight q q*weight q n)/(K*weight q q)
    rw [← mul_assoc,mul_div_cancel_left₀ _ (mul_pos hk hw).ne']

private noncomputable def coprimeWeight (n : ℕ) : ℝ := if q∣n then 0 else weight q n

private lemma coprime_mul {a b : ℕ} (hc : a.Coprime b) :
    coprimeWeight q (a*b) = coprimeWeight q a*coprimeWeight q b := by
  simp only [coprimeWeight,(Fact.out : q.Prime).dvd_mul,weight_mul q hc]
  split_ifs <;> simp_all

private lemma coprime_summable (hs : Summable (weight q)) : Summable (coprimeWeight q) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro n; unfold coprimeWeight; split_ifs <;> simp [weight_nonneg]
  · intro n; unfold coprimeWeight; split_ifs <;> simp [weight_nonneg]

private lemma weight_difference (n : ℕ) :
    (1-ch q 2/2)*(weight q n - coprimeWeight q n) = amplitude q n := by
  rw [amplitude_eq,coprimeWeight]
  split_ifs <;> simp

private theorem coprime_factor (p : ℕ) (hp : p.Prime) (hq : q≠2) :
    ∑' e : ℕ, coprimeWeight q (p^e) = inertFactor q p := by
  by_cases he : p=q
  · subst p
    rw [tsum_eq_single 0]
    · simp [coprimeWeight,(Fact.out : q.Prime).not_dvd_one,weight_one,inertFactor,symbol_zero q (dvd_refl q)]
    · intro n hn
      simp [coprimeWeight,dvd_pow_self q hn]
  · have hpr := (Fact.out : q.Prime)
    have hN (e : ℕ) : ¬q∣p^e := fun h => he ((Nat.prime_dvd_prime_iff_eq hpr hp).mp (hpr.dvd_of_dvd_pow h)).symm
    simpa only [coprimeWeight,if_neg (hN _),if_neg he] using prime_factor q p hp hq

/-- The product over inert odd primes, in the unconditional product topology. -/
noncomputable def inertProduct : ℝ := ∏' p : Nat.Primes, inertFactor q p

private theorem product_value (hq : q≠2) (hA : Summable (amplitude q)) :
    HasProd (fun p : Nat.Primes => inertFactor q p) (inertProduct q) ∧
    (∑' n : ℕ, amplitude q n) = (1-ch q 2/2)*
      ((q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)))*inertProduct q := by
  have hw := weight_summable q hq hA
  have hh := coprime_summable q hw
  have hW := EulerProduct.eulerProduct_hasProd (weight_one q) (weight_mul q) hw.norm (weight_zero q)
  have h₁ : coprimeWeight q 1=1 := by simp [coprimeWeight,(Fact.out : q.Prime).not_dvd_one,weight_one]
  have h₀ : coprimeWeight q 0=0 := by simp [coprimeWeight]
  have hF := EulerProduct.eulerProduct_hasProd h₁ (coprime_mul q) hh.norm h₀
  have hI := hF.congr_fun (fun p : Nat.Primes => (coprime_factor q p p.property hq).symm)
  have hR : inertProduct q = ∑' n : ℕ, coprimeWeight q n := hI.tprod_eq
  let Q : Nat.Primes := ⟨q,Fact.out⟩
  let s := (q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1))
  have hcomb := (hasProd_ite_eq Q (1+s)).mul hI
  have he : ∑' n : ℕ, weight q n = (1+s)*(∑' n : ℕ, coprimeWeight q n) := hW.unique
    (hcomb.congr_fun fun p => by
      rw [prime_factor q p p.property hq]
      by_cases hp : p=Q
      · subst p
        simp [Q,s,inertFactor,symbol_zero q (dvd_refl q)]
        exact fun h => (h rfl).elim
      · have hp' : p.val ≠ q := fun h => hp (Subtype.ext h)
        simp [hp,hp'])
  have hs := ((hw.hasSum.sub hh.hasSum).mul_left (1-ch q 2/2)).congr_fun (fun n => (weight_difference q n).symm)
  refine ⟨hR ▸ hI,?_⟩
  rw [hs.tsum_eq,he,hR]
  dsimp only [s]
  ring

/-- Exact Euler product for every nonzero odd prime quadratic correlation. -/
theorem correlation_product (hAP : ThetaNaturalPrimeMeans.ProgressionMangoldt) (hq : q%4=3) :
    ∃ L : ℝ, 0<L ∧ Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L) ∧
      Tendsto (ThetaNaturalPrimeMeans.primeMean (fun p => (symbol q p:ℝ)*ThetaCharacterPrimeMeans.residual p))
        atTop (𝓝 ((parityFactor q:ℝ)*L*(1-(symbol q 2:ℝ)/2)*
          ((q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)))*inertProduct q)) := by
  obtain ⟨L,C,hl,hL,hC,hA⟩ := amplitude_sum q hAP hq
  obtain ⟨_,he⟩ := product_value q (by omega) hA.summable
  have hn : (parityFactor q:ℝ)*L ≠ 0 := mul_ne_zero (by exact_mod_cast parityFactor_nonzero q hq) hl.ne'
  rw [hA.tsum_eq,div_eq_iff hn] at he
  refine ⟨L,hl,hL,?_⟩
  convert hC using 2
  rw [he]
  ring

private lemma inertFactor_one_le (p : ℕ) : 1 ≤ inertFactor q p := by
  unfold inertFactor
  split_ifs <;> first | exact le_rfl | exact le_add_of_nonneg_right (by positivity)

/-- The finite inert-prime product through the inclusive cutoff n+2. -/
noncomputable def inertPrefix (n : ℕ) : ℝ := ∏ p∈(n+3).primesBelow,inertFactor q p

private noncomputable def ratio (n : ℕ) : ℝ := (((n:ℝ)+2)/(n+1))^2

private lemma primeStep (n : ℕ) : inertPrefix q (n+1)=inertPrefix q n*
    (if (n+3).Prime then inertFactor q (n+3) else 1) := by
  simp only [inertPrefix,Nat.primesBelow,prod_filter,show n+1+3=(n+3)+1 by omega,prod_range_succ]

private lemma step_bound (n : ℕ) :
    (if (n+3).Prime then inertFactor q (n+3) else 1)*ratio (n+1) ≤ ratio n := by
  unfold inertFactor ratio
  have hfix : (n:ℝ)+3-1 = n+2 := by ring
  have hdn : 0 < (n:ℝ)+2 := by positivity
  split_ifs <;> push_cast <;> try rw [hfix]
  all_goals
    field_simp [hdn.ne']
    nlinarith [Nat.cast_nonneg (α:=ℝ) n,
    sq_nonneg (n:ℝ),pow_nonneg (Nat.cast_nonneg (α:=ℝ) n) 3,
    pow_nonneg (Nat.cast_nonneg (α:=ℝ) n) 4,pow_nonneg (Nat.cast_nonneg (α:=ℝ) n) 5,
    pow_nonneg (Nat.cast_nonneg (α:=ℝ) n) 6]

private lemma prefix_one_le (n : ℕ) : 1 ≤ inertPrefix q n :=
  one_le_prod (fun p _ => inertFactor_one_le q p)

private lemma prefix_mono : Monotone (inertPrefix q) := monotone_nat_of_le_succ fun n => by
  rw [primeStep]
  apply le_mul_of_one_le_right (zero_le_one.trans (prefix_one_le q n))
  split_ifs <;> first | exact inertFactor_one_le q _ | exact le_rfl

private lemma certificate_antitone : Antitone (fun n => inertPrefix q n * ratio n) := antitone_nat_of_succ_le fun n => by
  simp only [primeStep,mul_assoc]
  exact mul_le_mul_of_nonneg_left (step_bound q n) (zero_le_one.trans (prefix_one_le q n))

private lemma ratio_one_le (n : ℕ) : 1 ≤ ratio n := by
  have h : 1 ≤ ((n:ℝ)+2)/(n+1) := (one_le_div (by positivity)).mpr (by linarith)
  exact one_le_pow₀ h

/-- At every cutoff the finite product and an explicit relative error enclose the
full product. The error bound is uniform in the quadratic conductor. -/
theorem product_interval (hq : q≠2) (hA : Summable (amplitude q)) (n : ℕ) :
    inertPrefix q n ≤ inertProduct q ∧ inertProduct q ≤ inertPrefix q n*(((n:ℝ)+2)/(n+1))^2 := by
  have hw := weight_summable q hq hA
  have hh := coprime_summable q hw
  have h₁ : coprimeWeight q 1=1 := by simp [coprimeWeight,(Fact.out : q.Prime).not_dvd_one,weight_one]
  have h₀ : coprimeWeight q 0=0 := by simp [coprimeWeight]
  have ht := EulerProduct.eulerProduct h₁ (coprime_mul q) hh.norm h₀
  have he (N : ℕ) : (∏ p∈N.primesBelow,∑' e : ℕ,coprimeWeight q (p^e)) =
      ∏ p∈N.primesBelow,inertFactor q p :=
    prod_congr rfl (fun p hp => coprime_factor q p (Nat.prime_of_mem_primesBelow hp) hq)
  have hI := (EulerProduct.eulerProduct_hasProd h₁ (coprime_mul q) hh.norm h₀).congr_fun
    (fun p : Nat.Primes => (coprime_factor q p p.property hq).symm)
  simp only [he,← hI.tprod_eq] at ht
  have H := ht.comp (tendsto_add_atTop_nat 3)
  change Tendsto (inertPrefix q) atTop (𝓝 (inertProduct q)) at H
  constructor
  · exact ge_of_tendsto H ((eventually_ge_atTop n).mono (fun _ h => prefix_mono q h))
  · apply le_of_tendsto H
    filter_upwards [eventually_ge_atTop n] with t ht'
    exact (le_mul_of_one_le_right (zero_le_one.trans (prefix_one_le q t)) (ratio_one_le t)).trans
      (certificate_antitone q ht')

/-- Uniform bounds for the inert Euler product. -/
theorem inertProduct_bounds (hq : q≠2) (hA : Summable (amplitude q)) : 1 ≤ inertProduct q ∧ inertProduct q ≤ 4 := by
  have H := product_interval q hq hA 0
  have h : (3:ℕ).primesBelow={2} := by decide
  norm_num [inertPrefix,h,inertFactor,show ¬ Odd 2 by decide] at H
  exact H

#print axioms product_interval

#print axioms inertProduct_bounds
#print axioms correlation_product
#print axioms weight_mul
#print axioms amplitude_eq
end Arxiv.«2501.03234».ThetaConductorProduct
