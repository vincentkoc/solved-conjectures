import ThetaReciprocalPrefixes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Additive reciprocity exchanges the fixed prime with the varying denominator. -/
namespace Arxiv.«2501.03234».ThetaAdditiveReciprocity
open Finset Real Complex ThetaReciprocalPrefixes
noncomputable section

theorem exchange {p D : ℕ} [Fact p.Prime] [NeZero D] (hc : p.Coprime D) (j : ℤ) :
    ZMod.stdAddChar ((j:ZMod p)/(D:ZMod p)) =
      ZMod.stdAddChar (-(j:ZMod D)*(p:ZMod D)⁻¹) *
        Complex.exp (Complex.I*((2*Real.pi*(j:ℝ)/((D:ℝ)*p):ℝ):ℂ)) := by
  let a := Nat.gcdA p D
  let b := Nat.gcdB p D
  have hbez : (1:ℤ)=(p:ℤ)*a+(D:ℤ)*b := by
    simpa only [hc.gcd_eq_one,Nat.cast_one] using Nat.gcd_eq_gcd_ab p D
  have hp := (Fact.out : p.Prime).pos
  have hD : 0<D := NeZero.pos _
  have hp' : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hD' : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
  have hpD : (D:ZMod p) * (b:ZMod p)=1 := by
    have h := congrArg (fun x : ℤ => (x:ZMod p)) hbez
    simpa using h.symm
  have hDp : (p:ZMod D) * (a:ZMod D)=1 := by
    have h := congrArg (fun x : ℤ => (x:ZMod D)) hbez
    simpa using h.symm
  have hu := ZMod.coe_mul_inv_eq_one p hc
  have hA : (a:ZMod D)=(p:ZMod D)⁻¹ := by
    calc
      _ = (a:ZMod D)*((p:ZMod D)*(p:ZMod D)⁻¹) := by rw [hu,mul_one]
      _ = ((p:ZMod D)*(a:ZMod D))*(p:ZMod D)⁻¹ := by ring
      _ = _ := by rw [hDp,one_mul]
  have hunit : (D:ZMod p)≠0 := left_ne_zero_of_mul_eq_one hpD
  have he₁ : (j:ZMod p)/(D:ZMod p) = ((j*b:ℤ):ZMod p) := by
    rw [div_eq_iff hunit,Int.cast_mul]
    calc
      _ = (j:ZMod p)*((D:ZMod p)*(b:ZMod p)) := by rw [hpD,mul_one]
      _ = _ := by ring
  have he₂ : -(j:ZMod D)*(p:ZMod D)⁻¹ = ((-j*a:ℤ):ZMod D) := by rw [←hA];push_cast;rfl
  rw [he₁,he₂,ZMod.stdAddChar_coe,ZMod.stdAddChar_coe,←Complex.exp_add]
  congr 1
  push_cast
  have hbc : (1:ℂ)=(p:ℂ)*(a:ℂ)+(D:ℂ)*(b:ℂ) := by exact_mod_cast hbez
  field_simp [hp',hD']
  linear_combination -(j:ℂ)*hbc

def row (p d : ℕ) (j : ℤ) : ℂ :=
  letI : NeZero (4*(d+1)) := ⟨by omega⟩
  ZMod.stdAddChar (-(j:ZMod (4*(d+1)))*(p:ZMod (4*(d+1)))⁻¹)

def horizontal (p N : ℕ) (j : ℤ) := ∑ d∈range N,row p d j

theorem depends_on_residue {p q N : ℕ} (j : ℤ)
    (hpq : p ≡ q [MOD 4*(range N).lcm (fun d => d+1)]) :
    horizontal p N j=horizontal q N j := by
  apply sum_congr rfl
  intro d hd
  have hdiv : d+1 ∣ (range N).lcm (fun n => n+1) := dvd_lcm hd
  have h := hpq.of_dvd (Nat.mul_dvd_mul_left 4 hdiv)
  have he := (ZMod.natCast_eq_natCast_iff ..).mpr h
  simp only [row,he]

theorem approximation {p N : ℕ} [Fact p.Prime] (ho : _root_.Odd p) (hN : N<p) (j : ℤ) :
    ‖recipSum N ((j:ZMod p)/4)-horizontal p N j‖ ≤
      Real.pi*|(j:ℝ)|/(2*p)*(harmonic N:ℝ) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hfour : p.Coprime 4 := ho.coprime_two_right.mul_right ho.coprime_two_right
  unfold recipSum horizontal
  rw [←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ d∈range N,(Real.pi*|(j:ℝ)|/(2*p))*((d+1:ℕ):ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      have hdp : d+1<p := by have := mem_range.mp hd;omega
      have hco := hfour.mul_right (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hdp))
      let : NeZero (4*(d+1)) := ⟨by omega⟩
      have he := exchange hco j
      rw [Nat.cast_mul,Nat.cast_ofNat,←div_div] at he
      rw [he]
      change ‖row p d j * _ - row p d j‖ ≤ _
      rw [←mul_sub_one,norm_mul,show ‖row p d j‖=1 by simp [row]]
      rw [one_mul]
      apply Real.norm_exp_I_mul_ofReal_sub_one_le.trans
      rw [Real.norm_eq_abs,abs_div,abs_mul,abs_mul]
      rw [abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos,
        abs_of_pos (show 0<((4*(d+1):ℕ):ℝ)*p by positivity)]
      push_cast
      apply le_of_eq
      field_simp
      ring
    _ = _ := by simp [harmonic,mul_sum]

#print axioms exchange
#print axioms depends_on_residue
#print axioms approximation
end
end Arxiv.«2501.03234».ThetaAdditiveReciprocity
