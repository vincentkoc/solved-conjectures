import ThetaReciprocalResonance

/-! Completing an ordinary initial reciprocal sum against a complete Kloosterman estimate. -/
namespace Arxiv.«2501.03234».ThetaInitialCompletion
open Finset Real Complex ThetaReciprocalPrefixes ThetaIntervalKernel ThetaReciprocalCutoff ThetaFourier
noncomputable section
variable {p : ℕ} [Fact p.Prime]
abbrev U (p : ℕ) := (ZMod p)ˣ

private lemma sum_initial_units {N : ℕ} (hN : N<p) (f : ZMod p → ℂ) :
    (∑ u : U p, if (u:ZMod p).val<N+1 then f (u:ZMod p) else 0) =
    ∑ j∈range N, f ((j+1 : ℕ):ZMod p) := by
  classical
  rw [←sum_filter]
  symm
  have hn (j : ℕ) (hj : j∈range N) : (↑(j+1):ZMod p)≠0 := by
    intro h
    have e := congrArg ZMod.val h
    have := mem_range.mp hj
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at e
    omega
  apply sum_bij (fun (j : ℕ) hj => Units.mk0 (↑(j+1):ZMod p) (hn j hj))
  · intro j hj
    have h := mem_range.mp hj
    simp only [mem_filter,mem_univ,true_and,Units.val_mk0,ZMod.val_natCast_of_lt (show j+1<p by omega)]
    omega
  · intro i hi j hj h
    have he := congrArg (fun u : U p => (u:ZMod p).val) h
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    dsimp only [Units.val_mk0] at he
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at he
    omega
  · intro u hu
    have h := (mem_filter.mp hu).2
    have hpos := (ZMod.val_pos.mpr u.ne_zero)
    refine ⟨(u:ZMod p).val-1,mem_range.mpr (by omega),Units.ext ?_⟩
    simp only [Units.val_mk0]
    rw [Nat.sub_add_cancel (by omega),ZMod.natCast_zmod_val]
  · intros; rfl

theorem completed {N : ℕ} (hN : N<p) (a : ZMod p) :
    (p:ℂ)*recipSum N a = ∑ t : ZMod p,series (N+1) (-t)*kloosterman t a := by
  classical
  let f (x : ZMod p) := ZMod.stdAddChar (a/x)
  change (p:ℂ)*(∑ j∈range N,f ((j+1:ℕ):ZMod p))=_
  rw [←sum_initial_units hN,mul_sum]
  calc
    _ = ∑ u : U p, ∑ t : ZMod p, series (N+1) (-t)*ZMod.stdAddChar (t*(u:ZMod p)+a*↑(u⁻¹)) := by
      apply sum_congr rfl
      intro u _
      have he := inversion (initial p (N+1)) (u:ZMod p)
      rw [show (p:ℂ)*(if (u:ZMod p).val<N+1 then f u else 0) =
        (p*(if (u:ZMod p)∈initial p (N+1) then 1 else 0):ℂ)*f u by
        simp only [initial,mem_filter,mem_univ,true_and]; split_ifs <;> simp]
      rw [←he,sum_mul]
      apply sum_congr rfl
      intro t _
      rw [amp_initial (by omega),AddChar.map_add_eq_mul]
      dsimp [f]
      rw [Units.val_inv_eq_inv_val,div_eq_mul_inv,mul_comm t]
      ring
    _ = _ := by
      rw [sum_comm]
      simp only [kloosterman,mul_sum]

theorem bounded {N : ℕ} (hp : p%2=1) (hN : N<p) (a : ZMod p) {B : ℝ} (hB : 0 ≤ B)
    (hk : ∀ t : ZMod p, ‖kloosterman t a‖ ≤ B) :
    ‖recipSum N a‖ ≤ (1+(harmonic (p/2):ℝ))*B := by
  have hspec : ∑ t : ZMod p,‖series (N+1) (-t)‖ ≤ (p:ℝ)*(1+harmonic (p/2)) := by
    rw [←sum_erase_add _ _ (mem_univ (0:ZMod p))]
    simp only [neg_zero,series_zero,Complex.norm_natCast]
    have h := sum_le_sum (s:=univ.erase (0:ZMod p)) (fun t ht =>
      (series_le_weight (N+1) (neg_ne_zero.mpr (mem_erase.mp ht).1)).trans_eq (weight_neg t))
    have hlen : (N:ℝ)+1 ≤ p := by exact_mod_cast hN
    push_cast
    linarith only [h.trans (weight_mass hp),hlen]
  have he := congrArg norm (completed hN a)
  rw [norm_mul,Complex.norm_natCast] at he
  have h1 := (le_of_eq he).trans (norm_sum_le ..)
  have h2 := sum_le_sum (s:=univ) (fun t _ => show ‖series (N+1) (-t)*kloosterman t a‖ ≤
    ‖series (N+1) (-t)‖*B from (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (hk t) (norm_nonneg _)))
  rw [←sum_mul] at h2
  have h3 := mul_le_mul_of_nonneg_right hspec hB
  apply (le_of_mul_le_mul_left _ (Nat.cast_pos.mpr (Fact.out : p.Prime).pos : 0<(p:ℝ)))
  linarith only [h1,h2,h3]

#print axioms completed
#print axioms bounded
end
end Arxiv.«2501.03234».ThetaInitialCompletion
