import ThetaDirichletRows
import ThetaQuadraticExcess
import Mathlib.Analysis.Fourier.ZMod

/-! Nonvanishing of the parity transform for every odd primitive Dirichlet character. -/
namespace Arxiv.«2501.03234».ThetaPrimitiveParity
open Finset Filter Topology Complex DirichletCharacter
open scoped ZMod ComplexConjugate
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem power_transform (hχ : χ.IsPrimitive) (n : ℕ) :
    ∑ a : ZMod q,χ a * ZMod.stdAddChar a^n=χ⁻¹ (n:ZMod q)*gaussSum χ ZMod.stdAddChar := by
  have he (a : ZMod q) : ZMod.stdAddChar a^n=(ZMod.stdAddChar.mulShift (n:ZMod q)) a := by
    rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul,AddChar.mulShift_apply]
  simp_rw [he]
  change gaussSum χ _=_
  exact gaussSum_mulShift_of_isPrimitive _ hχ _

theorem gauss_ne_zero (hχ : χ.IsPrimitive) : gaussSum χ ZMod.stdAddChar≠0 := by
  intro h
  have H : ZMod.dft (χ : ZMod q → ℂ)=0 := by
    funext n
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,h,mul_zero,Pi.zero_apply]
  have h0 := ZMod.dft.injective (H.trans (map_zero ZMod.dft).symm)
  have h1 := congrFun h0 1
  simp at h1

private theorem radial_sum (hχ : χ.IsPrimitive) {r : ℝ} (hr : 0<r) (hr' : r<1) :
    (∑ a : ZMod q, χ a * -log (1-(r:ℂ)*ZMod.stdAddChar a)) =
      gaussSum χ ZMod.stdAddChar * ∑' n : ℕ, ((χ⁻¹ (n:ZMod q))/(n:ℂ))*(r:ℂ)^n := by
  have h (a : ZMod q) : ‖(r:ℂ)*ZMod.stdAddChar a‖<1 := by
    simpa only [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos hr,ZMod.stdAddChar_apply,
      Circle.norm_coe,mul_one] using hr'
  have H := hasSum_sum (s:=univ) (fun a (_ : a∈(univ : Finset (ZMod q))) =>
    (Complex.hasSum_taylorSeries_neg_log (h a)).mul_left (χ a))
  have H' (n : ℕ) : (∑ a : ZMod q,χ a * (((r:ℂ)*ZMod.stdAddChar a)^n/n)) =
      gaussSum χ ZMod.stdAddChar * (χ⁻¹ (n:ZMod q)/(n:ℂ)*(r:ℂ)^n) := by
    have he (a : ZMod q) : χ a * (((r:ℂ)*ZMod.stdAddChar a)^n/n) =
        (χ a * ZMod.stdAddChar a^n)*((r:ℂ)^n/n) := by rw [mul_pow]; ring
    simp_rw [he,← sum_mul,power_transform χ hχ]; ring
  simp_rw [H'] at H
  rw [← H.tsum_eq,tsum_mul_left]


noncomputable def firstMoment : ℂ := ∑ a : ZMod q,χ a*(a.val:ℂ)

private theorem re_even (a : ZMod q) (r : ℝ) :
    (-log (1-(r:ℂ)*ZMod.stdAddChar (-a))).re=(-log (1-(r:ℂ)*ZMod.stdAddChar a)).re := by
  have hn : ‖ZMod.stdAddChar a‖=1 := by simp only [ZMod.stdAddChar_apply,Circle.norm_coe]
  have he : 1-(r:ℂ)*ZMod.stdAddChar (-a)=conj (1-(r:ℂ)*ZMod.stdAddChar a) := by
    rw [AddChar.map_neg_eq_inv,inv_eq_conj hn,map_sub,map_one,map_mul,conj_ofReal]
  simp only [he,neg_re,log_re,norm_conj]

private theorem radial_odd (hodd : χ.Odd) (r : ℝ) :
    ∑ a : ZMod q,χ a * -log (1-(r:ℂ)*ZMod.stdAddChar a)=
    I * ∑ a : ZMod q,χ a*((-log (1-(r:ℂ)*ZMod.stdAddChar a)).im:ℂ) := by
  let Z (a : ZMod q) := -log (1-(r:ℂ)*ZMod.stdAddChar a)
  let F (a : ZMod q) := χ a*(Z a).re
  have he (a : ZMod q) : F (-a)= -F a := by
    change χ (-a)*(_ : ℂ)=_
    rw [← neg_one_mul a,map_mul,hodd]
    simp only [F,Z,re_even,one_mul,neg_mul]
  have H := Equiv.sum_comp (Equiv.neg (ZMod q)) F
  simp only [Equiv.neg_apply,he,sum_neg_distrib] at H
  have hz : ∑ a,F a=0 := by linear_combination -H/2
  have hx (a : ZMod q) : χ a*Z a=F a+I*(χ a*(Z a).im) := by
    dsimp [F]
    nth_rw 1 [←re_add_im (Z a)]
    ring
  change (∑ a,χ a*Z a)=_
  simp_rw [hx,sum_add_distrib,hz,zero_add,←mul_sum]
  rfl

private theorem weighted_im (hq1 : 1<q) (a : ZMod q) :
    Tendsto (fun r : ℝ => χ a*((-log (1-(r:ℂ)*ZMod.stdAddChar a)).im:ℂ)) (𝓝[<] 1)
      (𝓝 (χ a*((Real.pi/2-Real.pi*a.val/q:ℝ):ℂ))) := by
  by_cases ha : a=0
  · simp [ha,χ.map_zero' (by omega : q≠1)]
  · let t := Real.pi*a.val/q
    have hp := NeZero.pos q
    have hv : 0<a.val := Nat.pos_of_ne_zero (fun h => ha ((ZMod.val_eq_zero a).mp h))
    have ht : 0<t := by dsimp [t]; positivity
    have ht' : t<Real.pi := by
      dsimp [t]
      rw [div_lt_iff₀ (by positivity : (0:ℝ)<q)]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast ZMod.val_lt a) Real.pi_pos
    have hψ : ZMod.stdAddChar a=exp (((2*t:ℝ):ℂ)*I) := by
      rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
      congr 1; dsimp [t]; push_cast; ring
    rw [hψ]
    exact (continuous_ofReal.continuousAt.tendsto.comp (ThetaQuadraticExcess.radial_argument ht ht')).const_mul _

/-- For a primitive odd character the first moment is a nonzero multiple of the
Gauss sum and the inverse character's ordinary L-value. -/
theorem moment_identity (hχ : χ.IsPrimitive) (hodd : χ.Odd) (hq1 : 1<q) :
    gaussSum χ ZMod.stdAddChar*LFunction χ⁻¹ 1= -(I*Real.pi/(q:ℂ))*firstMoment χ := by
  have hne : χ≠1 := by
    intro h
    have H : χ.conductor=q := hχ
    rw [h,conductor_one] at H; omega
  have hpre := (ThetaCharacterHarmonicLimit.harmonic_limit χ⁻¹ (inv_ne_one.mpr hne)).1
  have H := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hpre
  rw [tendsto_map'_iff] at H
  have hr := H.const_mul (gaussSum χ ZMod.stdAddChar)
  have hl := (tendsto_finsetSum univ (fun a _ => weighted_im χ hq1 a)).const_mul I
  have he : gaussSum χ ZMod.stdAddChar*LFunction χ⁻¹ 1=
      I*(∑ a : ZMod q,χ a*((Real.pi/2-Real.pi*a.val/q:ℝ):ℂ)) := by
    apply tendsto_nhds_unique_of_eventuallyEq hr hl
    filter_upwards [self_mem_nhdsWithin,(eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono
      (nhdsWithin_le_nhds (s:=Set.Iio (1:ℝ)))] with r h1 h0
    change gaussSum χ ZMod.stdAddChar*(∑' n : ℕ,χ⁻¹ (n:ZMod q)/n*(r:ℂ)^n)=_
    rw [←radial_sum χ hχ h0 h1,radial_odd χ hodd]
  rw [he,firstMoment]
  push_cast
  simp_rw [mul_sub,sum_sub_distrib,←sum_mul,χ.sum_eq_zero_of_ne_one hne,zero_mul,zero_sub]
  simp_rw [show ∀ a : ZMod q,χ a*((Real.pi:ℂ)*a.val/q)=((Real.pi:ℂ)/q)*(χ a*a.val) by intro a; ring,←mul_sum]
  ring

private lemma parity_double (ho : Odd q) (a : ZMod q) :
    (q:ℤ)*ThetaCharacterThree.parity (2*a).val =
      4*(a.val:ℤ)-2*((2*a).val:ℤ)-q := by
  have hq := Nat.odd_iff.mp ho
  have ha := a.val_lt
  rw [show (2:ZMod q)*a=a+a by ring,ZMod.val_add]
  by_cases h : q≤a.val+a.val
  · rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    have hp : Odd (a.val+a.val-q) := Nat.odd_iff.mpr (by omega)
    rw [ThetaCharacterThree.parity,hp.neg_one_pow,neg_neg,mul_one]
    omega
  · rw [Nat.mod_eq_of_lt (by omega),ThetaCharacterThree.parity,(show Even (a.val+a.val) from ⟨a.val,rfl⟩).neg_one_pow]
    push_cast; ring

private lemma residue_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ a : ZMod q,f a.val=∑ j∈range q,f j := by
  rw [←Fin.sum_univ_eq_sum_range]
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

/-- Doubling the residue in the first moment gives the parity transform without
a choice of Gauss-sum orientation. -/
theorem doubling (ho : Odd q) (hne : χ≠1) :
    (q:ℂ)*ThetaDirichletRows.parityFactor χ=(4*χ 2-2)*firstMoment χ := by
  let u := ZMod.unitOfCoprime 2 ho.coprime_two_left
  have hu : (u:ZMod q)=2 := by simp [u]
  have perm (f : ZMod q → ℂ) : (∑ a,f (2*a))=∑ a,f a := by
    rw [←hu]
    exact Equiv.sum_comp (Units.mulLeft u) f
  have hp : (∑ a : ZMod q,χ a*(ThetaCharacterThree.parity a.val:ℂ))=ThetaDirichletRows.parityFactor χ := by
    have H := residue_sum (q:=q) (fun j => (χ (j:ZMod q))*(ThetaCharacterThree.parity j:ℂ))
    simp only [ZMod.natCast_zmod_val] at H
    rw [H]
    exact sum_congr rfl (fun _ _ => mul_comm ..)
  rw [←hp,←perm (fun a => χ a*(ThetaCharacterThree.parity a.val:ℂ)),mul_sum]
  have term (a : ZMod q) :
      (q:ℂ)*(χ (2*a)*(ThetaCharacterThree.parity (2*a).val:ℂ))=
      (4*χ 2)*(χ a*a.val)-2*(χ (2*a)*(2*a).val)-q*(χ 2*χ a) := by
    have hp' : (q:ℂ)*(ThetaCharacterThree.parity (2*a).val:ℂ)=4*(a.val:ℂ)-2*((2*a).val:ℂ)-q := by
      exact_mod_cast parity_double ho a
    rw [map_mul]
    linear_combination (χ 2*χ a)*hp'
  simp_rw [term,sum_sub_distrib,←mul_sum]
  rw [perm (fun a => χ a*(a.val:ℂ)),χ.sum_eq_zero_of_ne_one hne]
  dsimp [firstMoment]; ring

theorem parity_nonzero (hχ : χ.IsPrimitive) (hodd : χ.Odd) (ho : Odd q) (hq : 1<q) :
    ThetaDirichletRows.parityFactor χ≠0 := by
  have hne : χ≠1 := by
    intro h
    have H : χ.conductor=q := hχ
    rw [h,conductor_one] at H; omega
  have hm : firstMoment χ≠0 := by
    intro h
    have H := moment_identity χ hχ hodd hq
    rw [h,mul_zero] at H
    exact (mul_ne_zero (gauss_ne_zero χ hχ) (LFunction_apply_one_ne_zero (inv_ne_one.mpr hne))) H
  have hu : ‖χ 2‖=1 := by
    let u := ZMod.unitOfCoprime 2 ho.coprime_two_left
    simpa [u] using χ.unit_norm_eq_one u
  have hc : 4*χ 2-2≠0 := by
    intro h
    have he : χ 2=1/2 := by linear_combination h/4
    rw [he] at hu
    norm_num [norm_div] at hu
  intro h
  have H := doubling χ ho hne
  rw [h,mul_zero] at H
  exact (mul_ne_zero hc hm) H.symm

theorem parity_zero (hχ : χ.IsPrimitive) (heven : χ.Even) (ho : Odd q) (hq : 1<q) :
    ThetaDirichletRows.parityFactor χ=0 := by
  have hne : χ≠1 := by
    intro h
    have H : χ.conductor=q := hχ
    rw [h,conductor_one] at H; omega
  have he (a : ZMod q) : χ (-a)*((-a).val:ℂ)=χ a*(q:ℂ)-χ a*(a.val:ℂ) := by
    by_cases ha : a=0
    · simp [ha,χ.map_zero' (by omega : q≠1)]
    · rw [heven.eval_neg,ZMod.neg_val,if_neg ha,Nat.cast_sub (ZMod.val_lt a).le]; ring
  have H := Equiv.sum_comp (Equiv.neg (ZMod q)) (fun a => χ a*(a.val:ℂ))
  simp only [Equiv.neg_apply,he,sum_sub_distrib,←sum_mul,χ.sum_eq_zero_of_ne_one hne,zero_mul,zero_sub] at H
  have hm : firstMoment χ=0 := by dsimp [firstMoment]; linear_combination -H/2
  have hD := doubling χ ho hne
  rw [hm,mul_zero] at hD
  exact (mul_eq_zero.mp hD).resolve_left (by exact_mod_cast NeZero.ne q)

#print axioms parity_zero
#print axioms doubling
#print axioms parity_nonzero
#print axioms gauss_ne_zero
#print axioms moment_identity
end Arxiv.«2501.03234».ThetaPrimitiveParity
