import ThetaPrimitiveSpectrum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! Change of conductor for prime Fourier coefficients of the mean-centered theta sum. -/
namespace Arxiv.«2501.03234».ThetaLevelCoefficients
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaDirichletRows ThetaCharacterPrimeMeans ThetaDiagonalConstant ThetaPeriodMeans
open scoped ComplexConjugate

noncomputable def centered (p : ℕ) : ℝ := residual p-diagonalConstant

theorem meanC_re (f : ℕ → ℂ) (X : ℕ) :
    (primeMeanC f X).re = primeMean (fun n => (f n).re) X := by
  simp [primeMeanC,primeMean]

theorem meanC_im (f : ℕ → ℂ) (X : ℕ) :
    (primeMeanC f X).im = primeMean (fun n => (f n).im) X := by
  simp [primeMeanC,primeMean]

theorem meanC_real (f : ℕ → ℝ) (X : ℕ) :
    primeMeanC (fun p => (f p:ℂ)) X = (primeMean f X:ℂ) := by
  simp [primeMeanC,primeMean]

/-- Finitely many primes where two summands differ leave the same complex prime-mean limit. -/
theorem replace_at_primes {f g : ℕ → ℂ} {C : ℂ}
    (he : ∀ᶠ p in atTop, p.Prime → f p=g p)
    (h : Tendsto (primeMeanC g) atTop (𝓝 C)) : Tendsto (primeMeanC f) atTop (𝓝 C) := by
  let d (p : ℕ) := f p-g p
  have hzero : Tendsto (primeMeanC d) atTop (𝓝 0) := by
    apply complex_limit
    · simp only [meanC_re,zero_re]
      apply prime_mean_of_convergence
      intro ε hε
      filter_upwards [he] with p hp hprime
      simpa only [d,hp hprime,sub_self,zero_re,abs_zero] using hε
    · simp only [meanC_im,zero_im]
      apply prime_mean_of_convergence
      intro ε hε
      filter_upwards [he] with p hp hprime
      simpa only [d,hp hprime,sub_self,zero_im,abs_zero] using hε
  have H := hzero.add h
  rw [zero_add] at H
  apply H.congr'
  filter_upwards with X
  simp only [primeMeanC,d,sum_sub_distrib,sub_div,sub_add_cancel]

private theorem large_prime_coprime {m p : ℕ} [NeZero m] (h : m<p) (hp : p.Prime) : p.Coprime m :=
  hp.coprime_iff_not_dvd.mpr (fun hh => h.not_ge (Nat.le_of_dvd (NeZero.pos m) hh))

private theorem constant_mean {w : ℕ → ℂ} {c : ℂ}
    (h : ∀ᶠ p in atTop, p.Prime → w p=c) : Tendsto (primeMeanC w) atTop (𝓝 c) := by
  apply replace_at_primes h
  apply tendsto_const_nhds.congr'
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hπ.eventually_ne_atTop 0] with X hX
  have hn : (X.primeCounting:ℂ)≠0 := by exact_mod_cast (by exact_mod_cast (show (X.primeCounting:ℝ)≠0 from hX) : X.primeCounting≠0)
  simp [primeMeanC,Nat.primesLE_card_eq_primeCounting,hn]

/-- Orthogonality on ordinary primes at a fixed positive level. -/
theorem character_mean {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hAP : ProgressionMangoldt) :
    Tendsto (primeMeanC (symbol χ)) atTop (𝓝 (if χ=1 then 1 else 0)) := by
  split_ifs with he
  · subst χ
    apply constant_mean
    filter_upwards [eventually_gt_atTop m] with p hp hprime
    exact MulChar.one_apply (by simpa only [ZMod.isUnit_iff_coprime] using large_prime_coprime hp hprime)
  · have hn : ¬χ.conductor∣1 := fun h => he ((eq_one_iff_conductor_eq_one (χ:=χ)).mpr (Nat.dvd_one.mp h))
    simpa only [ofReal_one,mul_one] using blind_limit χ hn hAP (g:=fun _ => 1) (fun _ => rfl)

local instance conductorNeZero {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

/-- The coefficient at general level, with the limiting mean removed. -/
noncomputable def value {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) : ℂ :=
  if χ=1 then 0 else if _root_.Odd χ.conductor then coefficient χ.primitiveCharacter else 0

theorem coefficient_limit {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hAP : ProgressionMangoldt) :
    Tendsto (primeMeanC (fun p => symbol χ p*(centered p:ℂ))) atTop (𝓝 (value χ)) := by
  by_cases hχ : χ=1
  · subst χ
    rw [value,if_pos rfl]
    have hmean := (S_second_order_prime_mean hAP).sub (tendsto_const_nhds (x:=diagonalConstant))
    rw [sub_self] at hmean
    have hc : Tendsto (primeMean centered) atTop (𝓝 0) := by
      apply hmean.congr'
      have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
      filter_upwards [hπ.eventually_ne_atTop 0] with X hX
      simp only [centered,ThetaCharacterPrimeMeans.residual,primeMean,sum_sub_distrib,sub_div,sum_const,nsmul_eq_mul,
        Nat.primesLE_card_eq_primeCounting]
      change (X.primeCounting:ℝ)≠0 at hX
      field_simp
    apply replace_at_primes (g:=fun p => (centered p:ℂ))
    · filter_upwards [eventually_gt_atTop m] with p hp hprime
      have h : symbol (1:DirichletCharacter ℂ m) p=1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr (large_prime_coprime hp hprime))
      rw [h,one_mul]
    · change Tendsto (fun X => primeMeanC _ X) atTop (𝓝 0)
      simpa only [meanC_real,Function.comp_def,ofReal_zero] using (continuous_ofReal.continuousAt.tendsto.comp hc)
  · have hq : 1<χ.conductor := by
      have hp := χ.conductor_ne_zero
      have hn := mt (eq_one_iff_conductor_eq_one (χ:=χ)).mpr hχ
      omega
    have H := (spectrum χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hq hAP).1
    have hfull : Tendsto (primeMeanC (fun p => symbol χ p*(residual p:ℂ))) atTop (𝓝 (value χ)) := by
      simp only [value,if_neg hχ]
      apply replace_at_primes (g:=fun p => symbol χ.primitiveCharacter p*(residual p:ℂ)) _ H
      filter_upwards [eventually_gt_atTop m] with p hp hprime
      have hh := χ.primitiveCharacter_apply_of_isCoprime (a:=(p:ℤ))
        (by exact_mod_cast Nat.isCoprime_iff_coprime.mpr (large_prime_coprime hp hprime))
      simpa only [symbol,Int.cast_natCast] using congrArg (·*(residual p:ℂ)) hh.symm
    have h0 := character_mean χ hAP
    rw [if_neg hχ] at h0
    have hc := hfull.sub (h0.mul_const (diagonalConstant:ℂ))
    rw [zero_mul,sub_zero] at hc
    apply hc.congr'
    filter_upwards with X
    simp only [primeMeanC,centered,ofReal_sub,mul_sub,sum_sub_distrib,sub_div,
      ← sum_mul]
    ring

#print axioms character_mean
#print axioms coefficient_limit
end Arxiv.«2501.03234».ThetaLevelCoefficients
