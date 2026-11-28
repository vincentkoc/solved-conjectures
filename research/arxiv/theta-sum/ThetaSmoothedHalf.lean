import ThetaIntervalKernel

/-! Upper and lower counts in a half interval from reciprocal exponential sums. -/

namespace Arxiv.«2501.03234».ThetaSmoothedHalf
open Finset ThetaFourier ThetaIntervalKernel
variable {p : ℕ} [NeZero p]

noncomputable def expSum (x : ℕ → ZMod p) (n : ℕ) (t : ZMod p) : ℂ :=
  ∑ i ∈ range n, ZMod.stdAddChar (x i * t)

def hits (x : ℕ → ZMod p) (n K : ℕ) : ℕ :=
  ∑ i ∈ range n, if (x i).val < K then 1 else 0

def pairs (x : ℕ → ZMod p) (n K L : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range L, if (x i + (j : ZMod p)).val < K then 1 else 0

lemma pairs_fourier (x : ℕ → ZMod p) (n K L : ℕ) (hK : K ≤ p) :
    (p : ℂ) * pairs x n K L =
      ∑ t : ZMod p, series K (-t) * series L t * expSum x n t := by
  classical
  unfold pairs
  push_cast
  rw [mul_sum]
  simp_rw [mul_sum]
  calc
    _ = ∑ i ∈ range n, ∑ j ∈ range L, ∑ t : ZMod p,
        (series K (-t) * ZMod.stdAddChar ((j : ZMod p) * t)) * ZMod.stdAddChar (x i * t) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      have h := inversion (initial p K) (x i + (j : ZMod p))
      simp only [initial, mem_filter, mem_univ, true_and] at h
      rw [← h]
      apply sum_congr rfl
      intro t _
      rw [← amp_initial hK, add_mul, AddChar.map_add_eq_mul]
      unfold initial
      ring
    _ = ∑ t : ZMod p, ∑ i ∈ range n, ∑ j ∈ range L,
        (series K (-t) * ZMod.stdAddChar ((j : ZMod p) * t)) * ZMod.stdAddChar (x i * t) := by
      simp_rw [sum_comm (s:=range L) (t:=@univ (ZMod p) _)]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro t _
      unfold expSum
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [← sum_mul, ← mul_sum]
      rfl

private lemma pair_error (x : ℕ → ZMod p) {n K L H : ℕ} (hK : K ≤ p)
    (hp : p % 2 = 1) (hH : 0 < H) (hHm : H ≤ p/2) {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ t : ZMod p, t ≠ 0 → ‖expSum x n t‖ ≤ E) :
    |(p : ℝ) * pairs x n K L - (K : ℝ)*L*n| ≤
      (2*((p:ℝ)*L*harmonic H+(p:ℝ)^2/H))*E := by
  have heq : ‖(p : ℂ) * pairs x n K L - (K : ℂ)*L*n‖ =
      |(p : ℝ) * pairs x n K L - (K : ℝ)*L*n| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [← heq, pairs_fourier x n K L hK, ← sum_erase_add _ _ (mem_univ (0 : ZMod p))]
  simp only [neg_zero, series_zero, expSum, mul_zero, AddChar.map_zero_eq_one, sum_const,
    card_range, nsmul_eq_mul, mul_one, add_sub_cancel_right]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t ∈ univ.erase (0 : ZMod p), profile L t * E := by
      apply sum_le_sum
      intro t ht
      rw [norm_mul, norm_mul]
      have ht₀ := (mem_erase.mp ht).1
      apply mul_le_mul _ (he t ht₀) (norm_nonneg _) (by unfold profile weight; positivity)
      apply mul_le_mul ((series_le_weight K (neg_ne_zero.mpr ht₀)).trans_eq (weight_neg t))
        (le_min (series_le_length ..) (series_le_weight L ht₀)) (norm_nonneg _)
        (by unfold weight; positivity)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (profile_mass hp hH hHm) hE

omit [NeZero p] in
lemma shift_hits (x : ℕ → ZMod p) (n m L : ℕ) :
    hits x n (m+1) * L ≤ pairs x n (m+L) L := by
  unfold hits pairs
  rw [sum_mul]
  apply sum_le_sum
  intro i _
  split_ifs with h
  · rw [one_mul]
    calc
      L = ∑ j ∈ range L, (1 : ℕ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        have hv := ZMod.val_add_le (x i) (j : ZMod p)
        have hvj : (j : ZMod p).val ≤ j := by rw [ZMod.val_natCast]; exact Nat.mod_le ..
        have hj' := mem_range.mp hj
        rw [if_pos (by omega)]
  · simp

theorem half_upper (x : ℕ → ZMod p) {n L H : ℕ}
    (hp : p % 2 = 1) (hL : 0 < L) (hLp : p/2+L ≤ p)
    (hH : 0 < H) (hHm : H ≤ p/2) {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ t : ZMod p, t ≠ 0 → ‖expSum x n t‖ ≤ E) :
    2*(hits x n (p/2+1) : ℝ) - n ≤
      2*(n:ℝ)*L/p + 4*((harmonic H : ℝ)+(p:ℝ)/(H*L))*E := by
  have hs := shift_hits x n (p/2) L
  have hs' : (hits x n (p/2+1) : ℝ) * L ≤ pairs x n (p/2+L) L := by exact_mod_cast hs
  have he' := (le_abs_self _).trans (pair_error x (L:=L) hLp hp hH hHm hE he)
  have hm : 2*((p/2 : ℕ) : ℝ) ≤ p := by exact_mod_cast (show 2*(p/2) ≤ p by omega)
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (NeZero.pos p)
  have hL₀ : (0 : ℝ) < L := by exact_mod_cast hL
  have hH₀ : (0 : ℝ) < H := by exact_mod_cast hH
  push_cast at he'
  have h1 := mul_le_mul_of_nonneg_left hs' hp₀.le
  have h2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ (L : ℝ)*n by positivity)
  field_simp [hp₀.ne', hH₀.ne', hL₀.ne'] at he' ⊢
  nlinarith [mul_le_mul_of_nonneg_right h1 hH₀.le, mul_le_mul_of_nonneg_right h2 hH₀.le]

#print axioms half_upper
end Arxiv.«2501.03234».ThetaSmoothedHalf
