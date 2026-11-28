import ThetaDirichletMeans
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries

/-! The complex Euler factors giving the prime-power conductor contribution. -/
namespace Arxiv.«2501.03234».ThetaDirichletEuler
open Finset Filter Topology Complex ThetaDirichletRows

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

noncomputable def factor (p : ℕ) : ℂ :=
  if p=2 then 0 else if p∣q then 1 else
    (1-symbol χ⁻¹ p)*(1-symbol χ p/(p:ℂ)) * ((p:ℝ)/(p-1):ℝ)

noncomputable def weight (n : ℕ) : ℂ :=
  (∏ p∈n.primeFactors,factor χ p)/(n:ℂ)^2

lemma factor_bound {p : ℕ} (hp : p.Prime) :
    ‖factor χ p‖ ≤ 2*((p:ℝ)+1)/(p-1) := by
  have h1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have h0 : (0:ℝ)<p := by linarith
  have h2 : (0:ℝ)<p-1 := by linarith
  have ha : ‖1-symbol χ⁻¹ p‖≤2 :=
    (norm_sub_le ..).trans (by simp only [norm_one]; linarith [χ⁻¹.norm_le_one (p:ZMod q)])
  have hb : ‖1-symbol χ p/(p:ℂ)‖≤1+1/(p:ℝ) := by
    apply (norm_sub_le ..).trans
    simp only [norm_one,norm_div,norm_natCast]
    gcongr
    exact χ.norm_le_one _
  unfold factor
  split_ifs
  · simp only [norm_zero]; positivity
  · rw [norm_one,le_div_iff₀ h2]; linarith
  · simp only [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (div_pos h0 h2)]
    calc _ ≤ 2*(1+1/(p:ℝ))*((p:ℝ)/(p-1)) := by gcongr
         _ = _ := by field_simp

private lemma factor_small {p : ℕ} (hp : p.Prime) (h : p≠3) :
    ‖factor χ p‖ ≤ (p:ℝ)^(3/4:ℝ) := by
  have h1 : (1:ℝ)≤p := by exact_mod_cast hp.one_le
  have hp0 : (0:ℝ)<p := by linarith
  by_cases h2 : p=2
  · simp [factor,h2,Real.rpow_nonneg]
  have h5 : (5:ℝ)≤p := by
    have ho := hp.eq_two_or_odd.resolve_left h2
    exact_mod_cast (show 5≤p by have := hp.two_le; omega)
  have hb := factor_bound χ hp
  have hb3 : ‖factor χ p‖≤3 := hb.trans ((div_le_iff₀ (by linarith)).2 (by linarith))
  apply hb3.trans
  apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity)
  rw [←Real.rpow_mul_natCast hp0.le]
  norm_num
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5) h5 3]

theorem summable_weight : Summable (fun n => ‖weight χ n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((Real.summable_nat_rpow.mpr (by norm_num : (-(5/4):ℝ) < -1)).mul_left 4)
  intro n
  by_cases hn : n=0
  · simp [hn,weight,Real.zero_rpow]
  have hp : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [weight,norm_div,norm_prod,norm_pow,norm_natCast]
  have hfac (p : ℕ) (h : p∈n.primeFactors) :
      ‖factor χ p‖≤(if p=3 then 4 else 1)*(p:ℝ)^(3/4:ℝ) := by
    by_cases h3 : p=3
    · subst p
      have hb := factor_bound χ (by decide : Nat.Prime 3)
      norm_num at hb ⊢
      have hpow : 1≤(3:ℝ)^(3/4:ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      linarith
    · simp only [if_neg h3,one_mul]
      exact factor_small χ (Nat.prime_of_mem_primeFactors h) h3
  have hsingle : (∏ p∈n.primeFactors,if p=3 then (4:ℝ) else 1)≤4 := by
    rw [prod_ite_eq']; split_ifs <;> norm_num
  calc _ ≤ (∏ p∈n.primeFactors,((if p=3 then 4 else 1)*(p:ℝ)^(3/4:ℝ)))/(n:ℝ)^2 :=
         div_le_div_of_nonneg_right (prod_le_prod (fun _ _ => norm_nonneg _) hfac) (sq_nonneg _)
       _ ≤ 4*((∏ p∈n.primeFactors,(p:ℝ)^(3/4:ℝ))/(n:ℝ)^2) := by
         rw [prod_mul_distrib,←mul_div_assoc]
         gcongr
       _ ≤ 4*((n:ℝ)^(3/4:ℝ)/(n:ℝ)^2) := by
         apply mul_le_mul_of_nonneg_left _ (by norm_num)
         rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
         apply div_le_div_of_nonneg_right _ (sq_nonneg _)
         apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
         rw [←Nat.cast_prod]
         exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
       _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_sub hp]; norm_num

private lemma weight_mul {m n : ℕ} (hmn : m.Coprime n) :
    weight χ (m*n)=weight χ m*weight χ n := by
  by_cases hm : m=0
  · simp [hm,weight]
  by_cases hn : n=0
  · simp [hn,weight]
  simp only [weight,Nat.primeFactors_mul hm hn,prod_union hmn.disjoint_primeFactors,Nat.cast_mul]
  ring

private theorem local_series {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ,weight χ (p^e)=1+factor χ p/((p:ℂ)^2-1) := by
  have h1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  let r := ((p:ℂ)^2)⁻¹
  have hr : ‖r‖<1 := by
    simp only [r,norm_inv,norm_pow,norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have he (e : ℕ) : weight χ (p^(e+1))=(factor χ p*r)*r^e := by
    rw [weight,Nat.primeFactors_prime_pow (Nat.succ_ne_zero _) hp,prod_singleton,Nat.cast_pow]
    simp only [r,inv_pow,div_eq_mul_inv]
    ring
  have H := ((hasSum_geometric_of_norm_lt_one hr).mul_left (factor χ p*r)).congr_fun he
  rw [tsum_eq_zero_add' (f:=fun e : ℕ => weight χ (p^e)) H.summable,pow_zero,show weight χ 1=1 by simp [weight],H.tsum_eq]
  congr 1
  dsimp [r]
  have h0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  have ht : (p:ℂ)^2-1≠0 := by
    have hz : (p:ℤ)^2-1≠0 := by
      have hs : (2:ℤ)≤p := by exact_mod_cast hp.two_le
      nlinarith
    exact_mod_cast hz
  field_simp

/-- Euler product over the primes, absolutely convergent by the Dirichlet-series bound. -/
theorem product_value :
    (∑' n,weight χ n)=∏' p : Nat.Primes,(1+factor χ p/(((p:ℕ):ℂ)^2-1)) := by
  rw [←EulerProduct.eulerProduct_tprod (show weight χ 1=1 by simp [weight]) (@weight_mul q χ)
    (summable_weight χ) (show weight χ 0=0 by simp [weight])]
  exact tprod_congr (fun p => local_series χ p.2)

/-- The real part of the local Dirichlet correction is nonnegative. -/
private theorem factor_re {p : ℕ} (hp : p.Prime) : 0≤(factor χ p).re := by
  have h1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have h0 : (0:ℝ)<p := by linarith
  unfold factor
  split_ifs with _ h
  · simp
  · simp
  · let z := symbol χ p
    have hre : z.re≤1 := (re_le_norm _).trans (χ.norm_le_one _)
    rw [←MulChar.star_eq_inv χ]
    change 0≤((1-star z)*(1-z/(p:ℂ))*((p:ℝ)/(p-1):ℝ)).re
    rw [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    apply mul_nonneg _ (div_nonneg h0.le (by linarith))
    simp only [star_def,mul_re,sub_re,sub_im,one_re,one_im,conj_re,conj_im,div_natCast_re,div_natCast_im,
      zero_sub,mul_neg,sub_neg_eq_add,zero_add]
    apply add_nonneg (mul_nonneg (sub_nonneg.mpr hre) (sub_nonneg.mpr ((div_le_one h0).mpr (by linarith)))) _
    rw [←mul_div_assoc]
    exact div_nonneg (mul_self_nonneg _) h0.le

theorem weight_sum_norm : 1≤‖∑' n,weight χ n‖ := by
  have h := EulerProduct.eulerProduct (show weight χ 1=1 by simp [weight]) (@weight_mul q χ)
    (summable_weight χ) (show weight χ 0=0 by simp [weight])
  apply ge_of_tendsto h.norm
  filter_upwards with N
  rw [norm_prod]
  apply Finset.one_le_prod
  intro p hp
  have hpr := Nat.prime_of_mem_primesBelow hp
  have h1 : (1:ℝ)<p := by exact_mod_cast hpr.one_lt
  rw [local_series χ hpr]
  apply le_trans _ (re_le_norm _)
  have he : (p:ℂ)^2-1=(((p:ℝ)^2-1:ℝ):ℂ) := by push_cast; rfl
  rw [he,add_re,one_re,div_ofReal_re]
  linarith [div_nonneg (factor_re χ hpr) (by nlinarith : 0≤(p:ℝ)^2-1)]

#print axioms product_value
#print axioms summable_weight
#print axioms weight_sum_norm
end Arxiv.«2501.03234».ThetaDirichletEuler
