import ThetaAdditiveReciprocity
import ThetaShortMultiplier

/-! A large reciprocal sum with small numerator gives a large sum over varying moduli. -/
namespace Arxiv.«2501.03234».ThetaHorizontalWitness
open Finset Filter Real Asymptotics ThetaAdditiveReciprocity ThetaReciprocalPrefixes
open ThetaShortMultiplier ThetaReciprocalResonance
noncomputable section

def horizontalSignal (p N : ℕ) : Prop :=
  ∃ j : ℤ, j≠0 ∧ |(j:ℝ)| ≤ 2199023255552*(N:ℝ)*(log N)^2 ∧
    (N:ℝ)/(268435456*log N*log (log N)) < ‖horizontal p N j‖

private theorem log_fit : ∀ᶠ p : ℕ in atTop, 2^71*(log (p:ℝ))^5 ≤ p := by
  have h := ((isLittleO_log_rpow_rpow_atTop 5 (by norm_num : (0:ℝ)<1)).natCast_atTop).bound
    (by norm_num : (0:ℝ)<1/2^71)
  filter_upwards [h,eventually_ge_atTop (1:ℕ)] with p h hp
  change ‖(log (p:ℝ))^(5:ℝ)‖ ≤ (1/2^71:ℝ)*‖(p:ℝ)^(1:ℝ)‖ at h
  have hl : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast hp)
  rw [show (5:ℝ)=(5:ℕ) by norm_num,rpow_natCast,rpow_one,Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Nat.cast_nonneg _)] at h
  linarith

theorem transfer : ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ N : ℕ, exp (sqrt (log p)/512) ≤ N → N<p → shortSignal (p:=p) N → horizontalSignal p N := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [log_fit,hlog.eventually_ge_atTop (2048^2)] with p hfit hu
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro N hlo hn hcert
  obtain ⟨j,hj,hmag,hs⟩ := hcert
  refine ⟨j,fun h => hj (by simp [h]),hmag,?_⟩
  let u := log (p:ℝ)
  let v := log (N:ℝ)
  have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hN : 0<(N:ℝ) := (exp_pos _).trans_le hlo
  have hroot := sqrt_le_sqrt hu
  change sqrt (2048^2:ℝ) ≤ sqrt u at hroot
  rw [sqrt_sq (by norm_num : (0:ℝ) ≤ 2048)] at hroot
  have hh := (le_log_iff_exp_le hN).mpr hlo
  have hv : 3≤v := by change sqrt u/512 ≤ v at hh;linarith
  have hv₀ : 0<v := by linarith
  have hvu : v≤u := log_le_log hN (by exact_mod_cast hn.le)
  have hu₀ : 0<u := lt_of_lt_of_le hv₀ hvu
  have hw : 0<log v := log_pos (by linarith)
  have hwu : log v≤u := (log_le_sub_one_of_pos hv₀).trans (by linarith)
  have hH : (harmonic N:ℝ) ≤ 2*u := (harmonic_le_one_add_log _).trans (by change 1+v ≤ 2*u;linarith)
  have hA : Real.pi*|(j:ℝ)|/(2*p)*(harmonic N:ℝ) ≤ 8796093022208*N*u^3/(p:ℝ) := by
    have h₀ : (0:ℝ)≤harmonic N := by simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast];positivity
    calc
      _ ≤ (4*(2199023255552*(N:ℝ)*u^2)/(2*p))*(2*u) := by
        apply mul_le_mul _ hH h₀ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul Real.pi_lt_four.le _ (abs_nonneg _) (by norm_num)
        apply hmag.trans
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv₀.le hvu 2) (by positivity)
      _ = _ := by ring
  have hsmall : 8796093022208*N*u^3/(p:ℝ) ≤ (N:ℝ)/(268435456*u^2) := by
    apply (div_le_div_iff₀ hp₀ (by positivity)).mpr
    change 2^71*u^5 ≤ (p:ℝ) at hfit
    nlinarith only [mul_le_mul_of_nonneg_left hfit (Nat.cast_nonneg N)]
  have hden : 268435456*v*log v ≤ 268435456*u^2 := by
    calc
      _ ≤ 268435456*u*u := mul_le_mul (mul_le_mul_of_nonneg_left hvu (by norm_num)) hwu hw.le (by positivity)
      _ = _ := by ring
  have herr := (approximation ho hn j).trans (hA.trans (hsmall.trans
    (div_le_div_of_nonneg_left hN.le (by positivity) hden)))
  have hnrm := norm_sub_norm_le (recipSum N ((j:ZMod p)/4)) (horizontal p N j)
  change (N:ℝ)/(134217728*v*log v) < _ at hs
  change (N:ℝ)/(268435456*v*log v) < _
  have hx : (N:ℝ)/(134217728*v*log v)=2*((N:ℝ)/(268435456*v*log v)) := by ring
  rw [hx] at hs
  linarith only [hs,hnrm,herr]

theorem witness {δ : ℝ} (hδ : 0<δ) : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
    (S p:ℝ) ≤ (p:ℝ)*log p/100 → ∃ N : ℕ,window p N δ ∧ horizontalSignal p N := by
  filter_upwards [ThetaShortMultiplier.witness hδ,transfer] with p h ht
  intro hp ho hsmall
  obtain ⟨N,hw,hs⟩ := h hp ho hsmall
  exact ⟨N,hw,ht hp ho N hw.1 hw.2.2 hs⟩

#print axioms transfer
#print axioms witness
end
end Arxiv.«2501.03234».ThetaHorizontalWitness
