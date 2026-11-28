import ThetaPointwiseCompletion
import ThetaPointwiseOrders

/-! Pointwise removal of all sufficiently low-order multiplicative characters
from the original prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaPointwiseCutoff
open Finset Filter Real Complex DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCompletion ThetaPointwiseOrders
open scoped Topology
noncomputable section

def nonprincipal (p : ℕ) [Fact p.Prime] : Finset (DirichletCharacter ℂ p) :=
  univ.filter (·≠1)

def high (p : ℕ) [Fact p.Prime] (B : ℝ) : ℝ :=
  (4/(p.totient:ℝ))*∑ χ∈(nonprincipal p).filter (fun χ => ¬(orderOf χ:ℝ)≤ B),(cubic χ).re

theorem finite {p : ℕ} [Fact p.Prime] (hp : _root_.Odd p) {B : ℝ} (hB : 0≤ B) :
    |(S p:ℝ)-high p B|≤ 8*B*(p-1).divisors.card*Real.sqrt p*(1+Real.log p)^3 := by
  classical
  let D := (nonprincipal p).filter (fun χ => (orderOf χ:ℝ)≤ B)
  let E := (nonprincipal p).filter (fun χ => ¬(orderOf χ:ℝ)≤ B)
  have hp' : p.Prime := Fact.out
  have hpos : 0<(p:ℝ) := Nat.cast_pos.mpr hp'.pos
  have hφ : 0<(p.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hp'.pos)
  have hsum := congrArg Complex.re (expansion hp)
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,zero_mul,sub_zero,Complex.re_sum] at hsum
  norm_num at hsum
  change (p.totient:ℝ)*(S p:ℝ)=4*∑ χ∈nonprincipal p,(cubic χ).re at hsum
  have hsep := sum_filter_add_sum_filter_not (nonprincipal p) (fun χ => (orderOf χ:ℝ)≤ B) (fun χ => (cubic χ).re)
  have heq : (S p:ℝ)-high p B=(4/(p.totient:ℝ))*∑ χ∈D,(cubic χ).re := by
    rw [←hsep] at hsum
    change (p.totient:ℝ)*(S p:ℝ)=4*((∑ χ∈D,(cubic χ).re)+∑ χ∈E,(cubic χ).re) at hsum
    unfold high; change _-_* (∑ χ∈E,(cubic χ).re)=_
    field_simp; linarith
  have hcount := count_orders hp B hB D (fun _ h => (mem_filter.mp h).2)
  have hlog : (harmonic (p/2):ℝ)≤ 1+Real.log p :=
    (harmonic_le_one_add_log _).trans (add_le_add_right (Real.log_le_log (by exact_mod_cast Nat.div_pos hp'.two_le (by decide))
      (by exact_mod_cast Nat.div_le_self p 2)) _)
  have hterm (χ) (hχ : χ∈D) : |(cubic χ).re|≤ (Real.sqrt p*(1+Real.log p))^3 := by
    have hne := (mem_filter.mp (mem_filter.mp hχ).1).2
    have hH : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (harmonic_pos (Nat.div_pos hp'.two_le (by decide)).ne').le
    exact (abs_re_le_norm _).trans ((cubic_bound hp χ hne).trans (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)) 3))
  have H := (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum hterm)
  simp only [sum_const,nsmul_eq_mul] at H
  have hlogp : 0≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp'.pos)
  have hb := H.trans (mul_le_mul_of_nonneg_right hcount (by positivity))
  have h2 : (p:ℝ)≤ 2*p.totient := by
    rw [Nat.totient_prime hp',Nat.cast_sub hp'.one_le]; push_cast
    have h : (2:ℝ)≤ p := by exact_mod_cast hp'.two_le
    linarith
  rw [heq,abs_mul,abs_of_nonneg (by positivity : 0≤ 4/(p.totient:ℝ))]
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans
  have hfactor : 4/(p.totient:ℝ)*(Real.sqrt p)^3≤ 8*Real.sqrt p := by
    rw [show (Real.sqrt p)^3=(p:ℝ)*Real.sqrt p by rw [pow_succ,Real.sq_sqrt hpos.le],←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [div_mul_eq_mul_div,div_le_iff₀ hφ]; linarith only [h2]
  calc _ = (4/(p.totient:ℝ)*(Real.sqrt p)^3)*(B*(p-1).divisors.card*(1+Real.log p)^3) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_right hfactor (by positivity)).trans_eq (by ring)

#print axioms finite
end
end Arxiv.«2501.03234».ThetaPointwiseCutoff
