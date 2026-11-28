import ThetaPrimitiveTwist
import ThetaCharacterHarmonicLimit
import ThetaCharacterThree

/-! A primitive odd character detecting the second ternary digit of prime denominators. -/
namespace Arxiv.«2501.03234».ThetaSexticNine
open Finset Filter Topology Complex DirichletCharacter

/-- The coordinates (2 Re χ(a), 2 Im χ(a)/√3). -/
private def coeff (a : ZMod 9) : ℤ × ℤ :=
  match a.val with
  | 1 => (2,0) | 2 => (1,1) | 4 => (-1,1) | 5 => (1,-1)
  | 7 => (-1,-1) | 8 => (-2,0) | _ => (0,0)

private noncomputable def value (a : ZMod 9) : ℂ :=
  ⟨((coeff a).1:ℝ)/2, Real.sqrt 3*((coeff a).2:ℝ)/2⟩

private theorem value_mul (a b : ZMod 9) : value (a*b)=value a*value b := by
  have pair : ∀ a b : ZMod 9,
      2*(coeff (a*b)).1=(coeff a).1*(coeff b).1-3*(coeff a).2*(coeff b).2 ∧
      2*(coeff (a*b)).2=(coeff a).1*(coeff b).2+(coeff a).2*(coeff b).1 := by decide
  obtain ⟨hr,hi⟩ := pair a b
  have hR : 2*((coeff (a*b)).1:ℝ)=(coeff a).1*(coeff b).1-3*((coeff a).2:ℝ)*(coeff b).2 := by exact_mod_cast hr
  have hI : 2*((coeff (a*b)).2:ℝ)=(coeff a).1*((coeff b).2:ℝ)+((coeff a).2:ℝ)*(coeff b).1 := by exact_mod_cast hi
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  apply Complex.ext
  · change _ = (value a).re*(value b).re-(value a).im*(value b).im
    dsimp [value]
    linear_combination hR/4+((coeff a).2:ℝ)*(coeff b).2*h3/4
  · change _ = (value a).re*(value b).im+(value a).im*(value b).re
    dsimp [value]
    linear_combination Real.sqrt 3*hI/4

/-- The odd primitive complex character modulo 9 taking 2 to exp(πi/3). -/
noncomputable def chi : DirichletCharacter ℂ 9 where
  toFun := value
  map_one' := by
    have h : coeff 1=(2,0) := by decide
    apply Complex.ext <;> simp [value,h]
  map_mul' := value_mul
  map_nonunit' a ha := by
    have h : ¬a.val.Coprime 9 := fun h => ha (by simpa using (ZMod.isUnit_iff_coprime a.val 9).2 h)
    have H : ∀ x : ZMod 9, ¬x.val.Coprime 9 → coeff x=(0,0) := by decide
    apply Complex.ext <;> simp [value,H a h]

theorem chi_odd : chi.Odd := by
  have h : coeff (-1)=(-2,0) := by decide
  change value (-1)= -1
  apply Complex.ext <;> norm_num [value,h]

theorem chi_primitive : chi.IsPrimitive := by
  let u : (ZMod 9)ˣ := ZMod.unitOfCoprime 4 (by decide)
  have hu : (u:ZMod 9)=4 := rfl
  have hu3 : ZMod.unitsMap (show 3∣9 by decide) u=1 := by
    apply Units.ext
    change ZMod.cast (u:ZMod 9)=(1:ZMod 3)
    rw [hu]
    decide
  have hn : ¬chi.FactorsThrough 3 := by
    intro h
    have hker := (factorsThrough_iff_ker_unitsMap (show 3∣9 by decide)).mp h
    have he : chi.toUnitHom u=1 := hker (show u∈(ZMod.unitsMap (show 3∣9 by decide)).ker from hu3)
    have H := congrArg (fun v : ℂˣ => (v:ℂ).re) he
    rw [MulChar.coe_toUnitHom,hu] at H
    have hc : coeff 4=(-1,1) := by decide
    change (value 4).re=1 at H
    norm_num [value,hc] at H
  have hdiv := chi.conductor_dvd_level
  have hnot : ¬chi.conductor∣3 := fun h => hn ((mem_conductorSet_iff_conductor_dvd chi (by decide : 3∣9)).mpr h)
  change chi.conductor=9
  have hle := Nat.le_of_dvd (by decide : 0<9) hdiv
  interval_cases χc : chi.conductor <;> simp_all


theorem chi_nonprincipal : chi≠1 := by
  intro h
  have hC := chi_primitive
  change chi.conductor=9 at hC
  rw [h,conductor_one] at hC
  contradiction

/-- A short exact harmonic prefix separates the L-value from zero quantitatively. -/
theorem harmonic_real_lower : (1:ℝ)/2 < (LFunction chi 1).re := by
  let B : ℂ := ∑ n∈range 18,chi (n:ZMod 9)/(n:ℂ)
  have hp : B.re=2943819/2722720 := by
    simp only [B,re_sum,div_natCast_re]
    change ∑ n∈range 18,(((coeff (n:ZMod 9)).1:ℝ)/2)/(n:ℝ)=_
    norm_num [sum_range_succ,coeff,ZMod.val_natCast]
  have H := ThetaCharacterHarmonicLimit.harmonic_error chi chi_nonprincipal (K:=18) (by decide)
  have hl : B.re-(LFunction chi 1).re≤(9:ℝ)/18 := by
    rw [←sub_re]
    apply (re_le_norm _).trans
    rw [norm_sub_rev]
    exact H
  linarith

/-- The real part of the conductor's conjugate parity transform is exactly two. -/
theorem parity_real :
    (∑ j∈range 9,(ThetaCharacterThree.parity j:ℂ)*chi⁻¹ (j:ZMod 9)).re=2 := by
  rw [← MulChar.star_eq_inv chi]
  simp only [re_sum,MulChar.star_apply,mul_re,intCast_re,intCast_im,zero_mul,sub_zero,star_def,conj_re]
  change ∑ j∈range 9,(ThetaCharacterThree.parity j:ℝ)*(((coeff (j:ZMod 9)).1:ℝ)/2)=_
  norm_num [sum_range_succ,coeff,ZMod.val_natCast,ThetaCharacterThree.parity]

theorem parity_norm :
    ‖∑ j∈range 9,(ThetaCharacterThree.parity j:ℂ)*chi⁻¹ (j:ZMod 9)‖=4 := by
  have hi : (∑ j∈range 9,(ThetaCharacterThree.parity j:ℂ)*chi⁻¹ (j:ZMod 9)).im=2*Real.sqrt 3 := by
    rw [←MulChar.star_eq_inv chi]
    simp only [im_sum,MulChar.star_apply,mul_im,intCast_re,intCast_im,zero_mul,add_zero,star_def,conj_im]
    change ∑ j∈range 9,(ThetaCharacterThree.parity j:ℝ)*(-(Real.sqrt 3*((coeff (j:ZMod 9)).2:ℝ)/2))=_
    norm_num [sum_range_succ,coeff,ZMod.val_natCast,ThetaCharacterThree.parity]
    ring
  rw [norm_eq_sqrt_sq_add_sq,parity_real,hi]
  have h : (2:ℝ)^2+(2*Real.sqrt 3)^2=16 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  rw [h]; norm_num

theorem two_norm : ‖1-chi (2:ZMod 9)/2‖=Real.sqrt 3/2 := by
  have h : coeff 2=(1,1) := by decide
  rw [norm_eq_sqrt_sq_add_sq]
  simp only [sub_re,sub_im,div_ofNat_re,div_ofNat_im,one_re,one_im]
  change Real.sqrt ((1-(value 2).re/2)^2+(0-(value 2).im/2)^2)=_
  simp only [value,h,Int.cast_one,mul_one]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  nlinarith

#print axioms parity_norm
#print axioms two_norm
#print axioms harmonic_real_lower
#print axioms parity_real

#print axioms chi_odd
#print axioms chi_primitive
end Arxiv.«2501.03234».ThetaSexticNine
