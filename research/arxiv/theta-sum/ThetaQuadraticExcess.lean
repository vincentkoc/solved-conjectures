import ThetaPrimeSpectrum
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The endpoint Fourier coefficient of the odd quadratic harmonic series. -/
namespace Arxiv.«2501.03234».ThetaQuadraticExcess
open Finset Filter Topology Complex ThetaLegendreFactors

theorem radial_argument {t : ℝ} (ht : 0<t) (ht' : t<Real.pi) :
    Tendsto (fun r : ℝ => (-log (1-(r:ℂ)*exp (((2*t:ℝ):ℂ)*I))).im)
      (𝓝[<] 1) (𝓝 (Real.pi/2-t)) := by
  let z := exp (((2*t:ℝ):ℂ)*I)
  have hs := Real.sin_pos_of_pos_of_lt_pi ht ht'
  have hzre : 0 < (1-z).re := by
    simp only [z,sub_re,one_re,exp_ofReal_mul_I_re,Real.cos_two_mul_eq_one_sub]
    nlinarith [sq_pos_of_pos hs]
  have hlog : ContinuousAt (fun r : ℝ => -log (1-(r:ℂ)*z)) 1 := by
    apply ContinuousAt.neg
    apply ContinuousAt.clog
    · fun_prop
    · simpa using (mem_slitPlane_iff.mpr (Or.inl hzre))
  have he : 1-z = ((2*Real.sin t:ℝ):ℂ)*exp (((t-Real.pi/2:ℝ):ℂ)*I) := by
    apply Complex.ext <;>
      simp only [z,sub_re,one_re,sub_im,one_im,mul_re,mul_im,ofReal_re,ofReal_im,zero_mul,sub_zero,add_zero,
        exp_ofReal_mul_I_re,exp_ofReal_mul_I_im,Real.cos_sub_pi_div_two,Real.sin_sub_pi_div_two,
        Real.cos_two_mul_eq_one_sub,Real.sin_two_mul] <;> ring
  have hi : (((t-Real.pi/2:ℝ):ℂ)*I).im = t-Real.pi/2 := by simp
  have hb : (-log (1-z)).im = Real.pi/2-t := by
    rw [he,log_ofReal_mul (by positivity) (exp_ne_zero _),
      log_exp (by rw [hi]; linarith [Real.pi_pos]) (by rw [hi]; linarith [Real.pi_pos])]
    simp
  have h := (continuous_im.continuousAt.comp hlog).tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Iio 1))
  change Tendsto (fun r : ℝ => (-log (1-(r:ℂ)*z)).im) (𝓝[<] 1) (𝓝 ((-log (1-((1:ℝ):ℂ)*z)).im)) at h
  simpa only [ofReal_one,one_mul,hb] using h

variable (q : ℕ) [Fact q.Prime]

noncomputable def tau : ℂ := gaussSum (dirChar q) ZMod.stdAddChar

private lemma power_transform (hq : q≠2) (n : ℕ) :
    ∑ a : ZMod q, dirChar q a * ZMod.stdAddChar a ^ n = (dirChar q (n:ZMod q)) * tau q := by
  have he (a : ZMod q) : ZMod.stdAddChar a ^ n =
      (ZMod.stdAddChar.mulShift (n : ZMod q)) a := by
    rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul,AddChar.mulShift_apply]
  simp_rw [he]
  change gaussSum (dirChar q) _ = _
  by_cases hn : (n:ZMod q)=0
  · simp only [hn,gaussSum,AddChar.mulShift_apply,zero_mul,AddChar.map_zero_eq_one,mul_one]
    rw [(dirChar q).sum_eq_zero_of_ne_one (nonprincipal q hq)]
    simp [dirChar]
  · let u := (isUnit_iff_ne_zero.mpr hn).unit
    have hh := gaussSum_mulShift_eq (dirChar q) ZMod.stdAddChar u
    have hinv := ((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)).inv
    simpa only [u,IsUnit.unit_spec,show (dirChar q)⁻¹=dirChar q from hinv,tau] using hh

private theorem radial_sum (hq : q≠2) {r : ℝ} (hr : 0<r) (hr' : r<1) :
    (∑ a : ZMod q, dirChar q a * -log (1-(r:ℂ)*ZMod.stdAddChar a)) =
      tau q * ∑' n : ℕ, ((dirChar q (n:ZMod q))/(n:ℂ))*(r:ℂ)^n := by
  have h (a : ZMod q) : ‖(r:ℂ)*ZMod.stdAddChar a‖<1 := by
    simpa only [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos hr,ZMod.stdAddChar_apply,
      Circle.norm_coe,mul_one] using hr'
  have H := hasSum_sum (s:=univ) (fun a (_ : a∈(univ : Finset (ZMod q))) =>
    (Complex.hasSum_taylorSeries_neg_log (h a)).mul_left (dirChar q a))
  have H' (n : ℕ) : (∑ a : ZMod q,dirChar q a * (((r:ℂ)*ZMod.stdAddChar a)^n/n)) =
      tau q * (dirChar q (n:ZMod q)/(n:ℂ)*(r:ℂ)^n) := by
    have he (a : ZMod q) : dirChar q a * (((r:ℂ)*ZMod.stdAddChar a)^n/n) =
        (dirChar q a * ZMod.stdAddChar a^n)*((r:ℂ)^n/n) := by rw [mul_pow]; ring
    simp_rw [he,← sum_mul,power_transform q hq]; ring
  simp_rw [H'] at H
  rw [← H.tsum_eq,tsum_mul_left]

private abbrev charVal (a : ZMod q) : ℤ := quadraticChar (ZMod q) a

/-- The first moment of the complete quadratic character period. -/
noncomputable def firstMoment : ℤ := ∑ a : ZMod q, charVal q a*(a.val:ℤ)

private lemma weighted_argument (a : ZMod q) :
    Tendsto (fun r : ℝ => (dirChar q a * -log (1-(r:ℂ)*ZMod.stdAddChar a)).im) (𝓝[<] 1)
      (𝓝 ((charVal q a:ℝ)*(Real.pi/2-Real.pi*a.val/q))) := by
  have H (z : ℂ) : (dirChar q a*z).im = (charVal q a:ℝ)*z.im := by
    change (((charVal q a:ℝ):ℂ)*z).im = _
    simp
  simp only [H]
  by_cases ha : a=0
  · subst a; simp [charVal]
  · apply Tendsto.const_mul
    let t := Real.pi*a.val/q
    have hq' := (Fact.out : q.Prime).pos
    have h0 : 0<a.val := Nat.pos_of_ne_zero (fun h => ha ((ZMod.val_eq_zero a).mp h))
    have ht : 0<t := by dsimp [t]; positivity
    have ht' : t<Real.pi := by
      dsimp [t]
      rw [div_lt_iff₀ (by positivity : (0:ℝ)<q)]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast ZMod.val_lt a) Real.pi_pos
    have hψ : ZMod.stdAddChar a = exp (((2*t:ℝ):ℂ)*I) := by
      rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
      congr 1; dsimp [t]; push_cast; ring
    simpa only [hψ] using radial_argument ht ht'

/-- Abel's limit theorem identifies the signed first moment without choosing a Gauss-sum root. -/
theorem gauss_times_harmonic (hq : q≠2) {L : ℝ}
    (hL : Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L)) :
    (tau q).im*L = -Real.pi*(firstMoment q:ℝ)/q := by
  have hpre : Tendsto (fun K => ∑ n∈range K,(dirChar q (n:ZMod q))/(n:ℂ)) atTop (𝓝 (L:ℂ)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have h := continuous_ofReal.continuousAt.tendsto.comp hL
    change Tendsto (fun K => ((ThetaCharacterSeven.siftedSum (term q) ∅ K:ℝ):ℂ)) atTop _ at h
    simpa only [ThetaCharacterSeven.siftedSum,ThetaCharacterSeven.sift,notMem_empty,
      IsEmpty.forall_iff,implies_true,if_true,term,Complex.ofReal_sum,Complex.ofReal_div,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Function.comp_def,dirChar,
      MulChar.ringHomComp_apply,Int.coe_castRingHom,symbol] using h
  have H := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hpre
  rw [tendsto_map'_iff] at H
  have hr := (continuous_im.continuousAt.tendsto.comp (H.const_mul (tau q)))
  have hl := tendsto_finsetSum univ (fun a _ => weighted_argument q a)
  have he : (tau q*(L:ℂ)).im = ∑ a : ZMod q,(charVal q a:ℝ)*(Real.pi/2-Real.pi*a.val/q) := by
    apply tendsto_nhds_unique_of_eventuallyEq hr hl
    filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono
      (nhdsWithin_le_nhds (s:=Set.Iio (1:ℝ)))] with r h1 h0
    change (tau q*(∑' n : ℕ,dirChar q (n:ZMod q)/n*(r:ℂ)^n)).im = _
    rw [← radial_sum q hq h0 h1,Complex.im_sum]
  have hz : ∑ a : ZMod q,(charVal q a:ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero (F:=ZMod q) (by simpa [ZMod.ringChar_zmod_n] using hq)
  rw [Complex.im_mul_ofReal] at he
  rw [he]
  simp only [firstMoment,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  simp_rw [mul_sub,sum_sub_distrib,← sum_mul,hz,zero_mul,zero_sub]
  simp_rw [show ∀ a : ZMod q, (charVal q a:ℝ)*(Real.pi*a.val/q)=
    (Real.pi/q)*((charVal q a:ℝ)*a.val) by intro a; ring,← mul_sum]
  ring

/-- The lower-half excess in a prime Legendre period. -/
noncomputable def excess : ℤ := ∑ j∈range (q/2),symbol q (j+1)

private lemma sum_val {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ a : ZMod q,f a.val = ∑ j∈range q,f j := by
  rw [← Fin.sum_univ_eq_sum_range]
  cases q with
  | zero => exact (Nat.not_prime_zero Fact.out).elim
  | succ q => rfl

private lemma upper_sum (hq : q%4=3) :
    (∑ a : ZMod q, if q≤2*a.val then charVal q a else 0) = -excess q := by
  have hv (a : ZMod q) : charVal q a = symbol q a.val := by simp only [charVal,symbol,ZMod.natCast_zmod_val]
  simp_rw [hv]
  rw [sum_val q (fun j => if q≤2*j then symbol q j else 0)]
  let k := q/2
  have hk : q=(k+1)+k := by dsimp [k];omega
  have H₁ (j : ℕ) (hj : j∈range (k+1)) : ¬ q≤2*j := by have := mem_range.mp hj;omega
  have H₂ (j : ℕ) : q ≤ 2*((k+1)+j) := by omega
  have he : (∑ j∈range (k+1), if q≤2*j then symbol q j else 0)=0 :=
    sum_eq_zero fun j hj => if_neg (H₁ j hj)
  rw [show range q=range ((k+1)+k) by rw [← hk],sum_range_add,he,zero_add]
  simp only [if_pos (H₂ _)]
  have hz := range_zero q (by omega)
  rw [show range q=range ((k+1)+k) by rw [← hk],sum_range_add,sum_range_succ',
    symbol_zero q (dvd_zero q),add_zero] at hz
  change _ = -(∑ j∈range k,symbol q (j+1))
  omega

/-- Doubling the residues relates their first moment to the excess. -/
theorem doubling_identity (hq : q%4=3) :
    (symbol q 2 - 2)*firstMoment q = q*excess q := by
  have hn : ¬q∣2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  let two : (ZMod q)ˣ := ZMod.unitOfCoprime 2 ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hn).symm
  have htwo : (two:ZMod q)=2 := by simp [two]
  have htwo0 : (2:ZMod q) ≠ 0 := htwo ▸ two.ne_zero
  have hperm := Equiv.sum_comp (Equiv.mulLeft₀ (2:ZMod q) htwo0)
    (fun a : ZMod q => charVal q a*(a.val:ℤ))
  change (∑ a : ZMod q,charVal q (2*a)*((2*a).val:ℤ))=firstMoment q at hperm
  have hchar (a : ZMod q) : charVal q (2*a)=symbol q 2*charVal q a := by
    change quadraticChar (ZMod q) (2*a)=quadraticChar (ZMod q) (2:ℕ)*quadraticChar (ZMod q) a
    rw [map_mul]; norm_num
  have hval (a : ZMod q) : ((2*a).val:ℤ) = 2*(a.val:ℤ)-(if q≤2*a.val then q else 0 : ℤ) := by
    rw [show (2:ZMod q)*a=a+a by ring,ZMod.val_add]
    have := ZMod.val_lt a
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hsum (a : ZMod q) : charVal q (2*a)*((2*a).val:ℤ) =
      symbol q 2*(2*(charVal q a*(a.val:ℤ))-(q:ℤ)*(if q≤2*a.val then charVal q a else 0)) := by
    rw [hchar,hval]; split_ifs <;> ring
  simp_rw [hsum,← mul_sum,sum_sub_distrib,← mul_sum,upper_sum q hq] at hperm
  change symbol q 2*(2*firstMoment q - q*(-excess q))=firstMoment q at hperm
  rcases symbol_unit q hn with h|h <;> rw [h] at hperm ⊢ <;> linarith

/-- The signed excess formula with the imaginary part of the actual Gauss sum. -/
theorem excess_eq_gauss (hq : q%4=3) {L : ℝ}
    (hL : Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L)) :
    (excess q:ℝ) = (2-(symbol q 2:ℝ))*(tau q).im*L/Real.pi := by
  have h := gauss_times_harmonic q (by omega) hL
  have hd := congrArg (Int.cast (R:=ℝ)) (doubling_identity q hq)
  push_cast at hd
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [eq_div_iff Real.pi_ne_zero]
  rw [eq_div_iff hq0] at h
  apply (mul_right_cancel₀ hq0)
  linear_combination Real.pi * -hd - ((2:ℝ)-(symbol q 2:ℝ))*h

/-- Squaring fixes the magnitude of the Gauss sum's imaginary part on the pinned mathlib alone. -/
theorem abs_tau_im (hq : q%4=3) : |(tau q).im| = Real.sqrt q := by
  have hχ : dirChar q (-1) = -1 := by
    have hh := quadraticChar_neg_one (F:=ZMod q) (by rw [ZMod.ringChar_zmod_n]; omega)
    rw [ZMod.card,ZMod.χ₄_nat_three_mod_four hq] at hh
    change ((quadraticChar (ZMod q) (-1):ℤ):ℂ) = -1
    exact_mod_cast hh
  have h := gaussSum_sq (nonprincipal q (by omega))
    ((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)) (ZMod.isPrimitive_stdAddChar q)
  change tau q ^2 = dirChar q (-1)*↑(Fintype.card (ZMod q)) at h
  rw [hχ,ZMod.card,neg_one_mul,pow_two] at h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [mul_im,neg_im,natCast_im,neg_zero,mul_re,natCast_re,neg_re] at him hre
  have hq0 := (Fact.out : q.Prime).pos
  have hqR : (0:ℝ)<q := by exact_mod_cast hq0
  have hi : (tau q).im ≠ 0 := by intro hi; rw [hi] at hre; nlinarith [sq_nonneg (tau q).re]
  have hr : (tau q).re=0 := by
    have hz : (tau q).re * (tau q).im = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_right hi
  rw [hr] at hre
  rw [← Real.sqrt_sq_eq_abs]
  congr 1; nlinarith

/-- Unconditional absolute form of the quadratic-excess formula. -/
theorem abs_excess (hq : q%4=3) {L : ℝ} (hpos : 0<L)
    (hL : Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L)) :
    |(excess q:ℝ)| = (2-(symbol q 2:ℝ))*Real.sqrt q*L/Real.pi := by
  have hn : ¬q∣2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hχ : 0≤2-(symbol q 2:ℝ) := by rcases symbol_unit q hn with h|h <;> norm_num [h]
  rw [excess_eq_gauss q hq hL,abs_div,abs_mul,abs_mul,abs_of_nonneg hχ,abs_tau_im q hq,
    abs_of_pos hpos,abs_of_pos Real.pi_pos]

#print axioms gauss_times_harmonic
#print axioms doubling_identity
#print axioms excess_eq_gauss
#print axioms abs_tau_im
#print axioms abs_excess
end Arxiv.«2501.03234».ThetaQuadraticExcess
