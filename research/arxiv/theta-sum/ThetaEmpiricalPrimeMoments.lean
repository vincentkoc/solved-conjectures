import ThetaFiniteTailMoments

/-! Finite empirical moments with an order uniform in the prime endpoint. -/
namespace Arxiv.«2501.03234».ThetaEmpiricalPrimeMoments
open Finset Filter Real ThetaPrimeQuantiles
noncomputable section

theorem scale {t j : ℝ} (ht : 1≤t) (hj : 1≤j) (L : ℝ) :
    height L (t*j)≤j^4*height L t := by
  have ht' : 0<t := by linarith
  have hj' : 0<j := by linarith
  have hl := log_nonneg ht
  have hl' := log_nonneg hj
  have he : 1+log (t*j)≤j*(1+log t) := by
    rw [log_mul ht'.ne' hj'.ne']
    nlinarith only [log_le_sub_one_of_pos hj',mul_le_mul_of_nonneg_right hj hl]
  have h₂ := pow_le_pow_left₀ (by rw [log_mul ht'.ne' hj'.ne'];linarith : 0≤1+log (t*j)) he 2
  have h₄ := pow_le_pow_right₀ hj (by decide : 2≤4)
  unfold height
  rw [mul_pow,show (t^2*j^2/L)^2=j^4*(t^2/L)^2 by ring]
  nlinarith only [h₂,mul_le_mul_of_nonneg_right h₄ (sq_nonneg (1+log t))]

/-- One endpoint threshold works for every positive integer order. -/
theorem original : ∃ D : ℝ, 0<D ∧ ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 1 ≤ m →
    ∑ p∈Nat.primesLE X, |(S p:ℝ)/p-log p/2|^m ≤ Nat.primeCounting X*
      (D*((1+log (m:ℝ))^2+(m:ℝ)^4/(log X)^2))^m := by
  classical
  obtain ⟨C,hC,hb⟩ := ThetaPrimeQuantiles.original
  refine ⟨2*C*16^4,by positivity,?_⟩
  filter_upwards [hb] with X hX
  intro m hm
  let L := log (X:ℝ)
  let t := 16*(m:ℝ)
  let B := C*height L t
  have hmr : (1:ℝ)≤ m := by exact_mod_cast hm
  have ht : 1≤t := by dsimp [t];linarith
  have hlog := log_nonneg ht
  have hB : 0<B := mul_pos hC (by unfold height;positivity)
  let P := Nat.primesLE X
  have hgrid (j : ℕ) (hj : 1≤j) :
      ((P.filter (fun p => B*(j:ℝ)^4≤residual p)).card:ℝ)≤P.card*exp (-(16*(m:ℝ)*j)) := by
    have hj' : (1:ℝ)≤j := by exact_mod_cast hj
    have H := hX (t*j) (one_le_mul_of_one_le_of_one_le ht hj')
    have hsub : P.filter (fun p => B*(j:ℝ)^4≤residual p)⊆
        ThetaMovingOriginalTail.exceptions (C*height L (t*j)) X := by
      intro p hp
      obtain ⟨hp,hh⟩ := mem_filter.mp hp
      obtain ⟨hl,hpr⟩ := Nat.mem_primesLE.mp hp
      apply ThetaPrimeQuantiles.member.mpr ⟨hl,hpr,?_⟩
      apply (mul_le_mul_of_nonneg_left (scale ht hj' L) hC.le).trans
      dsimp only [B] at hh;linarith only [hh]
    have hh := (Nat.cast_le.mpr (card_le_card hsub)).trans H
    simpa only [P,Nat.primesLE_card_eq_primeCounting,t] using hh
  have hmoment := ThetaFiniteTailMoments.finite P residual hB hm (fun _ => abs_nonneg _) hgrid
  let J := (1+log (m:ℝ))^2+(m:ℝ)^4/L^2
  have hid : height L m=J := by dsimp [height,J];rw [div_pow];ring
  have hu : B≤C*16^4*J := by
    have hs := scale hmr (by norm_num : (1:ℝ)≤16) L
    rw [hid,mul_comm (m:ℝ) 16] at hs
    exact (mul_le_mul_of_nonneg_left hs hC.le).trans_eq (by ring)
  have hm₂ : (2:ℝ)≤2^m := by simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hm)
  have hfinal : 2*B^m≤(2*C*16^4*J)^m := calc
    _ ≤ (2:ℝ)^m*B^m := mul_le_mul_of_nonneg_right hm₂ (pow_nonneg hB.le _)
    _ = (2*B)^m := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith only [hu]) _
  change _ ≤ Nat.primeCounting X*(2*C*16^4*J)^m
  apply hmoment.trans
  rw [show P.card=Nat.primeCounting X from Nat.primesLE_card_eq_primeCounting X]
  linarith only [mul_le_mul_of_nonneg_left hfinal (Nat.cast_nonneg (α:=ℝ) X.primeCounting)]

/-- The logarithmic-square moment bound holds in a growing order range,
including m² ≤ (log X)(1+log m). -/
theorem logarithmic : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 1 ≤ m →
    (m:ℝ)^2≤log X*(1+log (m:ℝ)) →
    ∑ p∈Nat.primesLE X, |(S p:ℝ)/p-log p/2|^m ≤ Nat.primeCounting X*
      (C*(1+log (m:ℝ))^2)^m := by
  obtain ⟨D,hD,h⟩ := original
  refine ⟨2*D,by positivity,?_⟩
  filter_upwards [h,(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 0] with X hX hL
  change 0<log (X:ℝ) at hL
  intro m hm hr
  apply (hX m hm).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hsmall : (m:ℝ)^4/(log X)^2≤(1+log (m:ℝ))^2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hL)]
    nlinarith only [pow_le_pow_left₀ (sq_nonneg (m:ℝ)) hr 2]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_left hsmall hD.le]

#print axioms original
#print axioms logarithmic
end
end Arxiv.«2501.03234».ThetaEmpiricalPrimeMoments
