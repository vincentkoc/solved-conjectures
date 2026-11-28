import ThetaSmoothedHalf
import ThetaShortFrequencies

/-! Smoothed parity discrepancy from a bounded range of signed frequencies. -/
namespace Arxiv.«2501.03234».ThetaTruncatedHalf
open Finset ThetaFourier ThetaIntervalKernel ThetaSmoothedHalf ThetaShortFrequencies
variable {p : ℕ} [NeZero p]

theorem pair_error (x : ℕ → ZMod p) {n K L H T : ℕ} (hK : K ≤ p)
    (hp : p%2=1) (hH : 0<H) (hHm : H≤p/2) (hT : 0<T) (hTm : T≤p/2)
    {E : ℝ} (hE : 0≤E) (he : ∀ t : ZMod p,t≠0 → near T t → ‖expSum x n t‖≤E) :
    |(p:ℝ)*pairs x n K L-(K:ℝ)*L*n| ≤
      (2*((p:ℝ)*L*harmonic H+(p:ℝ)^2/H))*E+(2*(p:ℝ)^2/T)*n := by
  classical
  have heq : ‖(p:ℂ)*pairs x n K L-(K:ℂ)*L*n‖=|(p:ℝ)*pairs x n K L-(K:ℝ)*L*n| := by
    rw [←Real.norm_eq_abs,←Complex.norm_real];push_cast;rfl
  rw [←heq,pairs_fourier x n K L hK,←sum_erase_add _ _ (mem_univ (0:ZMod p))]
  simp only [neg_zero,series_zero,expSum,mul_zero,AddChar.map_zero_eq_one,sum_const,
    card_range,nsmul_eq_mul,mul_one,add_sub_cancel_right]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t∈univ.erase (0:ZMod p), (profile L t*E+(if near T t then 0 else profile L t)*(n:ℝ)) := by
      apply sum_le_sum
      intro t ht
      have ht₀ := (mem_erase.mp ht).1
      have hprof : 0 ≤ profile L t := by unfold profile weight;positivity
      have hcoef : ‖series K (-t)‖*‖series L t‖≤profile L t :=
        mul_le_mul ((series_le_weight K (neg_ne_zero.mpr ht₀)).trans_eq (weight_neg t))
          (le_min (series_le_length ..) (series_le_weight L ht₀)) (norm_nonneg _) (by unfold weight;positivity)
      rw [norm_mul,norm_mul]
      apply (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans
      by_cases hn : near T t
      · simp only [if_pos hn,zero_mul,add_zero]
        exact mul_le_mul_of_nonneg_left (he t ht₀ hn) hprof
      · simp only [if_neg hn]
        have hlen : ‖expSum x n t‖≤n := (norm_sum_le ..).trans (by simp)
        exact (mul_le_mul_of_nonneg_left hlen hprof).trans (le_add_of_nonneg_left (mul_nonneg hprof hE))
    _ ≤ _ := by
      rw [sum_add_distrib,←sum_mul,←sum_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (profile_mass hp hH hHm) hE)
        (mul_le_mul_of_nonneg_right (tail_mass hp hT hTm) (Nat.cast_nonneg _))

theorem half (x : ℕ → ZMod p) {n L H T : ℕ} (hp : p%2=1) (hL : 0<L)
    (hLp : p/2+L≤p) (hH : 0<H) (hHm : H≤p/2) (hT : 0<T) (hTm : T≤p/2)
    {E : ℝ} (hE : 0≤E) (he : ∀ t : ZMod p, t≠0 → near T t → ‖expSum x n t‖≤E) :
    2*(hits x n (p/2+1):ℝ)-n ≤ 2*(n:ℝ)*L/p+4*((harmonic H:ℝ)+(p:ℝ)/(H*L))*E+
      4*((p:ℝ)/(T*L))*n := by
  have hs' : (hits x n (p/2+1):ℝ)*L ≤ pairs x n (p/2+L) L := by exact_mod_cast shift_hits x n (p/2) L
  have he' := (le_abs_self _).trans (pair_error x (L:=L) hLp hp hH hHm hT hTm hE he)
  have hm : 2*((p/2:ℕ):ℝ) ≤ p := by exact_mod_cast (show 2*(p/2)≤p by omega)
  have hp₀ : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  have hL₀ : (0:ℝ)<L := by exact_mod_cast hL
  have hH₀ : (0:ℝ)<H := by exact_mod_cast hH
  have hT₀ : (0:ℝ)<T := by exact_mod_cast hT
  push_cast at he'
  have h1 := mul_le_mul_of_nonneg_left hs' hp₀.le
  have h2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ (L:ℝ)*n by positivity)
  field_simp [hp₀.ne',hH₀.ne',hL₀.ne',hT₀.ne'] at he' ⊢
  have hp' := mul_pos hH₀ hT₀
  nlinarith only [he',mul_le_mul_of_nonneg_right h1 hp'.le,mul_le_mul_of_nonneg_right h2 hp'.le]

#print axioms half
end Arxiv.«2501.03234».ThetaTruncatedHalf
