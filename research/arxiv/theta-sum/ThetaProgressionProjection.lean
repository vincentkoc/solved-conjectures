import ThetaVarianceExhaustion
import ThetaDyadicLaw

/-! The best real congruence prediction is the limiting mean in each reduced prime class. -/
namespace Arxiv.«2501.03234».ThetaProgressionProjection
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaLevelCoefficients ThetaDirichletRows ThetaFiniteProjection ThetaVarianceExhaustion
open ThetaCharacterPrimeMeans ThetaDiagonalConstant ThetaPeriodMeans ThetaDyadicLaw ThetaPrimeDensity
open scoped ComplexConjugate
noncomputable section

private lemma inv_symbol {m : ℕ} (χ : DirichletCharacter ℂ m) (p : ℕ) :
    symbol χ⁻¹ p=conj (symbol χ p) := (MulChar.star_apply' χ _).symm

private lemma inv_value {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hAP : ProgressionMangoldt) :
    value χ⁻¹=conj (value χ) := by
  apply tendsto_nhds_unique (coefficient_limit χ⁻¹ hAP)
  apply (continuous_conj.continuousAt.tendsto.comp (coefficient_limit χ hAP)).congr'
  filter_upwards with X
  simp only [Function.comp_def,primeMeanC,map_div₀,map_sum,map_mul,conj_ofReal,map_natCast,inv_symbol]

/-- Conditional mean of the residual with its global mean removed. -/
def predictor (m : ℕ) [NeZero m] (p : ℕ) : ℝ := (model (value (m:=m)) p).re

theorem predictor_real (m : ℕ) [NeZero m] (p : ℕ) (hAP : ProgressionMangoldt) :
    (predictor m p:ℂ)=model (value (m:=m)) p := by
  have H := Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ m)) (fun χ => value χ*conj (symbol χ p))
  have he : conj (model (value (m:=m)) p)=model (value (m:=m)) p := by
    simpa only [model,map_sum,map_mul,conj_conj,Equiv.inv_apply,inv_value _ hAP,inv_symbol] using H
  apply Complex.ext
  · rfl
  · simpa only [ofReal_im] using (conj_eq_iff_im.mp he).symm

theorem optimal_error (m : ℕ) [NeZero m] {V : ℝ}
    (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V)) (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => (centered p-predictor m p)^2)) atTop (𝓝 (V-energy m)) := by
  have H := squared_error (m:=m) value hV hAP
  simpa only [←predictor_real _ _ hAP,←ofReal_sub,norm_real,Real.norm_eq_abs,sq_abs,
    sub_self,norm_zero,zero_pow (by decide : 2≠0),sum_const_zero,add_zero] using H

theorem predictor_periodic (m : ℕ) [NeZero m] : OnMod m (predictor m) := by
  intro n
  simp only [predictor,model,symbol,ZMod.natCast_mod]

def select {m : ℕ} (v : (ZMod m)ˣ) (p : ℕ) : ℝ := if (p:ZMod m)=(v:ZMod m) then 1 else 0

private theorem transform_select {m : ℕ} [NeZero m] (v : (ZMod m)ˣ) (χ : DirichletCharacter ℂ m) :
    transform m (select v) χ=χ (v:ZMod m)/m.totient := by
  classical
  simp only [transform,select,ZMod.natCast_zmod_val,Units.val_inj,apply_ite Complex.ofReal,
    ofReal_one,ofReal_zero,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,if_true]

theorem select_mean {m : ℕ} [NeZero m] (v : (ZMod m)ˣ) (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => centered p*select v p)) atTop
      (𝓝 (predictor m (v:ZMod m).val/m.totient)) := by
  let b := transform m (select v)
  have hperiod : OnMod m (select v) := fun n => by simp [select,ZMod.natCast_mod]
  have H := pairing (fun p => (centered p:ℂ)) value b (fun χ => by
    simpa only [mul_comm (centered _:ℂ)] using coefficient_limit χ hAP)
  have he : (∑ χ,value χ*conj (b χ)) = model (value (m:=m)) (v:ZMod m).val/m.totient := by
    simp only [b,transform_select,map_div₀,map_natCast,model,symbol,ZMod.natCast_zmod_val,mul_div_assoc,sum_div]
  rw [he] at H
  have T := continuous_re.continuousAt.tendsto.comp H
  simp only [Function.comp_def,meanC_re,div_natCast_re] at T
  apply primeMean_of_close _ T
  intro ε he
  filter_upwards [eventually_gt_atTop m] with p hp hprime
  have hh := hprime.coprime_iff_not_dvd.mpr (fun h => hp.not_ge (Nat.le_of_dvd (NeZero.pos m) h))
  simp only [b,inversion hperiod hh,conj_ofReal,←ofReal_mul,ofReal_re,sub_self,abs_zero]; exact he

/-- Mean inside each fixed reduced residue class, normalized by that class's own prime count. -/
theorem class_mean (m r : ℕ) [NeZero m] (hr : r.Coprime m) (hlt : r < m) (hAP : ProgressionMangoldt) :
    Tendsto (progressionMean m r centered) atTop (𝓝 (predictor m r)) := by
  let u := ZMod.unitOfCoprime r hr
  have hu : (u:ZMod m)=(r:ZMod m) := rfl
  have hv : (u:ZMod m).val=r := by rw [hu,ZMod.val_natCast,Nat.mod_eq_of_lt hlt]
  have H := select_mean u hAP
  rw [hv] at H
  have den := class_prime_density hAP (NeZero.pos m) hr hlt
  have hn : (m.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  have R := H.div den (one_div_ne_zero hn)
  rw [div_div_div_cancel_right₀ hn,div_one] at R
  apply R.congr'
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_ne_atTop 0] with X hX
  have hs : (∑ p∈Nat.primesLE X,centered p*select u p)=∑ p∈primeSet (fun n => n%m=r) X,centered p := by
    rw [primeSet,sum_filter]
    apply sum_congr rfl
    intro p _
    have hx : (p:ZMod m)=(u:ZMod m) ↔ p%m=r := by rw [←(ZMod.val_injective m).eq_iff,ZMod.val_natCast,hv]
    by_cases h : p%m=r <;> simp [select,hx,h]
  change (X.primeCounting:ℝ)≠0 at hX
  simp only [Pi.div_apply,progressionMean,primeMean,hs]
  field_simp

theorem original_mean (m r : ℕ) [NeZero m] (hr : r.Coprime m) (hlt : r < m) (hAP : ProgressionMangoldt) :
    Tendsto (progressionMean m r (fun p => (S p:ℝ)/p-Real.log p/2)) atTop
      (𝓝 (diagonalConstant+predictor m r)) := by
  have H := (class_mean m r hr hlt hAP).const_add diagonalConstant
  apply H.congr'
  filter_upwards [class_nonempty hAP (NeZero.pos m) hr hlt] with X hX
  have hn : ((primeSet (fun n => n%m=r) X).card:ℝ)≠0 := by exact_mod_cast hX.card_pos.ne'
  simp only [progressionMean,centered,ThetaCharacterPrimeMeans.residual,sum_sub_distrib,sum_const,nsmul_eq_mul]
  field_simp
  ring

#print axioms original_mean

#print axioms predictor_real
#print axioms optimal_error
#print axioms class_mean
end
end Arxiv.«2501.03234».ThetaProgressionProjection
