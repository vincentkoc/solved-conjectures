import ThetaReciprocalCutoff

/-! Odd representatives with odd inverse, estimated by the reciprocal parity discrepancy. -/
namespace Arxiv.«2501.03234».ThetaOddInverseCount
open Finset Filter Real ThetaFourier ThetaReciprocalCutoff ThetaCotangentTriangle
open scoped Topology
noncomputable section

def inverseCount (p : ℕ) [NeZero p] := ((odds p).filter (fun a => a⁻¹∈odds p)).card

theorem inverse_discrepancy {p : ℕ} [Fact p.Prime] (hp : p%2=1) :
    |2*(inverseCount p:ℝ)-(p/2:ℕ)|≤discrepancy p := by
  classical
  have H := reciprocal_interval (p:=p) hp 1 1 (p/2) (by simp) (Nat.div_le_self ..)
    (by intro i hi; omega)
  have hsum : ∑ i∈range (p/2),quotientSign p (1+2*i) 1 =
      ∑ x∈odds p, (if x⁻¹∈odds p then (1:ℤ) else -1) := by
    rw [←sum_progression hp]
    apply sum_congr rfl; intro i _
    simp only [quotientSign,Nat.cast_one,one_div,odds,mem_filter,mem_univ,true_and,add_comm 1]
  have hcount : ∑ x∈odds p,(if x⁻¹∈odds p then (1:ℤ) else -1) = 2*(inverseCount p:ℤ)-(p/2:ℕ) := by
    have ht (x : ZMod p) : (if x⁻¹∈odds p then (1:ℤ) else -1) =
        2*(if x⁻¹∈odds p then 1 else 0)-1 := by split_ifs <;> norm_num
    simp_rw [ht]
    rw [sum_sub_distrib,←mul_sum]
    simp [inverseCount,card_odds hp]
  rw [hsum,hcount] at H
  exact_mod_cast H

theorem discrepancy_small : ∀ᶠ p : ℕ in atTop, discrepancy p ≤ (p:ℝ)/8 := by
  have H : (fun p : ℕ => (log p)^2) =o[atTop] (fun p : ℕ => (p:ℝ)^(1/4:ℝ)) := by
    simpa only [rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/4)).natCast_atTop
  filter_upwards [H.bound (by norm_num : (0:ℝ)<1/288),eventually_ge_atTop 3] with p h hp
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have hx : 0<(p:ℝ) := by linarith
  have hl : 1≤log p := (Real.le_log_iff_exp_le hx).mpr (Real.exp_one_lt_three.le.trans hp')
  have hm : (harmonic (p/2):ℝ) ≤ 1+log p := (harmonic_le_one_add_log _).trans
    (add_le_add_right (log_le_log (by exact_mod_cast (show 0<p/2 by omega))
      (by exact_mod_cast Nat.div_le_self p 2)) _)
  have hn : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (harmonic_pos (by omega : p/2≠0)).le
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log (p:ℝ))),abs_of_pos (rpow_pos_of_pos hx _)] at h
  have hu : (1+(harmonic (p/2):ℝ))^2 ≤ 9*(log p)^2 := by
    calc _ ≤ (3*log p)^2 := pow_le_pow_left₀ (by linarith) (by linarith) _
         _ = _ := by ring
  have hpow : (p:ℝ)^(3/4:ℝ)*(p:ℝ)^(1/4:ℝ)=p := by
    rw [←rpow_add hx]; norm_num
  unfold discrepancy
  calc _ ≤ 4*(p:ℝ)^(3/4:ℝ)*(9*((1/288)*(p:ℝ)^(1/4:ℝ))) := by gcongr; exact hu.trans (by gcongr)
       _ = _ := by linarith only [hpow]

theorem eventually_many : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    (p:ℝ)/8 ≤ (inverseCount p:ℝ) := by
  filter_upwards [discrepancy_small,eventually_ge_atTop 4] with p h hp4
  intro hprime ho
  let : Fact p.Prime := ⟨hprime⟩
  have H := (abs_le.mp (inverse_discrepancy (Nat.odd_iff.mp ho))).1
  have hh : (2:ℝ)*((p/2:ℕ):ℝ)+1=p := by exact_mod_cast (show 2*(p/2)+1=p by have := Nat.odd_iff.mp ho; omega)
  have hp4' : (4:ℝ)≤p := by exact_mod_cast hp4
  linarith

#print axioms inverse_discrepancy
#print axioms eventually_many
end
end Arxiv.«2501.03234».ThetaOddInverseCount
