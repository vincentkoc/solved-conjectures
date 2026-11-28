import ThetaCompositeFourier
import Mathlib.Analysis.SpecificLimits.Basic

/-! Negative asymptotics for the original theta sum along powers of odd composite bases. -/
namespace Arxiv.«2501.03234».ThetaCompositePowers
open Finset Filter Topology ThetaCompositeFourier

/-- Leading coefficient of the normalized Pillai gcd sum along powers of a. -/
noncomputable def leading (a : ℕ) : ℝ :=
  ∏ p∈a.primeFactors,(a.factorization p:ℝ)*(1-1/(p:ℝ))

theorem leading_pos (a : ℕ) : 0<leading a := by
  apply prod_pos
  intro p hp
  have hfac : 0<a.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hpr := (Nat.prime_of_mem_primeFactors hp).one_lt
  have hpr' : (1:ℝ)<p := by exact_mod_cast hpr
  exact mul_pos (by exact_mod_cast hfac) (sub_pos.mpr ((div_lt_one (by positivity)).2 hpr'))

private theorem mass_limit {a : ℕ} (ha : a≠0) :
    Tendsto (fun n : ℕ => (gcdMass (a^n):ℝ)/(a:ℝ)^n/(n:ℝ)^a.primeFactors.card) atTop (𝓝 (leading a)) := by
  have hinv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have H := tendsto_finsetProd a.primeFactors (fun p _ => hinv.add_const ((a.factorization p:ℝ)*(1-1/(p:ℝ))))
  simp only [zero_add] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  change (∏ p∈a.primeFactors,(1/(n:ℝ)+(a.factorization p:ℝ)*(1-1/(p:ℝ))))=_
  rw [gcdMass_power_product ha n,←prod_const (s:=a.primeFactors) (b:=(n:ℝ)),←prod_div_distrib]
  apply prod_congr rfl
  intro p _
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

/-- The gcd sum captures the whole term of order larger than k log² k. -/
theorem log_error {k : ℕ} (hk : 1<k) (ho : Odd k) :
    |(S k:ℝ)/k+(1-1/(k:ℝ))/2*((gcdMass k:ℝ)/k-1)| ≤ 4*(1+Real.log k)^2 := by
  let : NeZero k := ⟨by omega⟩
  have hodd := Nat.odd_iff.mp ho
  have H := centered_gcd_bound (k:=k) hodd
  have hk' : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hm' : (2:ℝ)*(k/2:ℕ)+1=k := by exact_mod_cast (show 2*(k/2)+1=k by omega)
  have hm : ((k/2:ℕ):ℝ)=((k:ℝ)-1)/2 := by linarith
  have Hh := (harmonic_le_one_add_log (k/2)).trans (add_le_add_right
    (Real.log_le_log (by exact_mod_cast (show 0<k/2 by omega)) (show ((k/2:ℕ):ℝ)≤(k:ℝ) by exact_mod_cast Nat.div_le_self k 2)) 1)
  have hnonneg : (0:ℝ)≤harmonic (k/2) := by exact_mod_cast (show 0≤harmonic (k/2) by unfold harmonic; positivity)
  calc _ = |(k:ℝ)*S k+(k/2:ℕ)*((gcdMass k:ℝ)-k)|/(k:ℝ)^2 := by
         rw [←abs_of_nonneg (sq_nonneg (k:ℝ)),←abs_div,hm]
         congr 1
         field_simp
       _ ≤ 4*((k:ℝ)*harmonic (k/2))^2/(k:ℝ)^2 := div_le_div_of_nonneg_right H (sq_nonneg _)
       _ = 4*(harmonic (k/2):ℝ)^2 := by field_simp
       _ ≤ _ := by gcongr

private theorem error_limit {a : ℕ} (ha : 1<a) (ho : Odd a) {r : ℕ} (hr : 3≤r) :
    Tendsto (fun n : ℕ =>
      ((S (a^n):ℝ)/(a:ℝ)^n + (1-1/(a:ℝ)^n)/2*((gcdMass (a^n):ℝ)/(a:ℝ)^n-1))/(n:ℝ)^r)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => 4*(1+Real.log a)^2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' _ hi
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have ha' : (1:ℝ)≤a := by exact_mod_cast ha.le
  have hl := Real.log_nonneg ha'
  have H := log_error (one_lt_pow₀ ha (by omega : n≠0)) (ho.pow (n:=n))
  rw [Nat.cast_pow,Real.log_pow] at H
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos hn0 _)]
  apply (div_le_div_of_nonneg_right H (by positivity)).trans
  calc _ ≤ 4*((n:ℝ)*(1+Real.log a))^2/(n:ℝ)^3 := by
         apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_right₀ hn' hr)
         gcongr; nlinarith
       _ = _ := by field_simp

/-- For every odd base a>1 with r≥3 distinct prime factors, S(aⁿ)/(aⁿ nʳ)
has an explicit strictly negative limit. -/
theorem fixed_base_asymptotic {a : ℕ} (ha : 1<a) (ho : Odd a) (hr : 3≤a.primeFactors.card) :
    Tendsto (fun n : ℕ => (S (a^n):ℝ)/((a:ℝ)^n*(n:ℝ)^a.primeFactors.card))
      atTop (𝓝 (-leading a/2)) := by
  let r := a.primeFactors.card
  have ha0 : a≠0 := by omega
  have hA : Tendsto (fun n : ℕ => 1/(a:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast ha))
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)^r) atTop atTop :=
    (tendsto_pow_atTop (by dsimp [r]; omega : r≠0)).comp tendsto_natCast_atTop_atTop
  have hN : Tendsto (fun n : ℕ => 1/(n:ℝ)^r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hc := ((tendsto_const_nhds (x:=(1:ℝ))).sub hA).div_const 2
  have hM := (mass_limit ha0).sub hN
  have H := (error_limit ha ho hr).sub (hc.mul hM)
  convert H.congr' _ using 2
  · ring
  · filter_upwards with n
    dsimp only [r]
    ring

theorem fixed_base_unbounded_below {a : ℕ} (ha : 1<a) (ho : Odd a) (hr : 3≤a.primeFactors.card) :
    Tendsto (fun n : ℕ => (S (a^n):ℝ)/(a:ℝ)^n) atTop atBot := by
  have h := fixed_base_asymptotic ha ho hr
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)^a.primeFactors.card) atTop atTop :=
    (tendsto_pow_atTop (by omega : a.primeFactors.card≠0)).comp tendsto_natCast_atTop_atTop
  have H := h.neg_mul_atTop (by linarith [leading_pos a]) hnat
  apply H.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

private theorem leading_105 : (105:ℕ).primeFactors.card=3 ∧ leading 105=16/35 := by
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have h7 : Nat.Prime 7 := by decide
  have hs : (105:ℕ).primeFactors={3,5,7} := by
    rw [show (105:ℕ)=3*5*7 by decide,Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),h3.primeFactors,h5.primeFactors,h7.primeFactors]
    decide
  have hf : (105:ℕ).factorization=(3:ℕ).factorization+(5:ℕ).factorization+(7:ℕ).factorization := by
    rw [show (105:ℕ)=3*5*7 by decide,Nat.factorization_mul (by decide) (by decide),Nat.factorization_mul (by decide) (by decide)]
  norm_num [hs,leading,hf,h3.factorization,h5.factorization,h7.factorization,Finsupp.single_apply]

/-- Explicit leading term on powers of 105=3·5·7. -/
theorem powers_105 :
    Tendsto (fun n : ℕ => (S (105^n):ℝ)/((105:ℝ)^n*(n:ℝ)^3)) atTop (𝓝 (-(8:ℝ)/35)) ∧
      Tendsto (fun n : ℕ => (S (105^n):ℝ)/(105:ℝ)^n) atTop atBot := by
  obtain ⟨hc,hL⟩ := leading_105
  have H := fixed_base_asymptotic (a:=105) (by decide) (by decide) (by omega)
  rw [hc,hL] at H
  exact ⟨by convert H using 2 <;> norm_num,
    fixed_base_unbounded_below (a:=105) (by decide) (by decide) (by omega)⟩

#print axioms powers_105

#print axioms log_error
#print axioms leading_pos
#print axioms fixed_base_asymptotic
#print axioms fixed_base_unbounded_below
end Arxiv.«2501.03234».ThetaCompositePowers
