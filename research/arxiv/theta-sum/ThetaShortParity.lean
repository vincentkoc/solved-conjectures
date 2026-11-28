import ThetaReciprocalParity
import ThetaTruncatedHalf

/-! A discrepancy bound for a reciprocal block using only short signed Fourier multipliers. -/
namespace Arxiv.«2501.03234».ThetaShortParity
open Finset ThetaCotangentTriangle ThetaShortReciprocalBlocks ThetaReciprocalParity ThetaSmoothedHalf
open ThetaShortFrequencies ThetaTruncatedHalf
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem signed (hp : p % 2 = 1) (x : ℕ → ZMod p) {n L H T : ℕ}
    (hx : ∀ j < n, x j ≠ 0) (hL : 0 < L) (hLp : p/2+L ≤ p)
    (hH : 0 < H) (hHm : H ≤ p/2) (hT : 0<T) (hTm : T≤p/2) {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ t : ZMod p, t ≠ 0 → near T t → ‖expSum x n t‖ ≤ E) :
    |∑ j ∈ range n, (if (2*x j).val % 2 = 1 then (1:ℝ) else -1)| ≤
      2*(n:ℝ)*L/p + 4*((harmonic H : ℝ)+(p:ℝ)/(H*L))*E+4*((p:ℝ)/(T*L))*n := by
  have hsum : (∑ j ∈ range n, (if (2*x j).val % 2 = 1 then (1:ℝ) else -1)) =
      n - 2*(hits x n (p/2+1) : ℝ) := by
    unfold hits
    push_cast
    rw [mul_sum]
    conv_rhs => lhs; rw [show (n : ℝ) = ∑ _j ∈ range n, (1 : ℝ) by simp]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    simp only [twice_odd hp]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have hen (t : ZMod p) (ht : t ≠ 0) (hn : near T t) :
      ‖expSum (fun j => -x j) n t‖ ≤ E := by
    simpa [expSum, neg_mul, mul_neg] using he (-t) (neg_ne_zero.mpr ht) (near_neg.mpr hn)
  have h₁ := half x hp hL hLp hH hHm hT hTm hE he
  have h₂ := half (fun j => -x j) hp hL hLp hH hHm hT hTm hE hen
  have hc := hits_complement hp x hx
  have hc' : (hits x n (p/2+1) : ℝ) + hits (fun j => -x j) n (p/2+1) = n := by exact_mod_cast hc
  rw [hsum, abs_le]
  constructor <;> linarith

theorem block (hp : p % 2 = 1) {a n k L H T : ℕ} (hk : k < p/2) (han : a+n ≤ p/2)
    (hL : 0 < L) (hLp : p/2+L ≤ p) (hH : 0 < H) (hHm : H ≤ p/2) (hT : 0<T) (hTm : T≤p/2)
    {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ t : ZMod p, t ≠ 0 → near T t →
      ‖∑ j ∈ range n, ZMod.stdAddChar ((denom p k/2*t) / denom p (a+j))‖ ≤ E) :
    |∑ j ∈ range n, sgn p (a+j) k| ≤
      2*(n:ℝ)*L/p + 4*((harmonic H : ℝ)+(p:ℝ)/(H*L))*E+4*((p:ℝ)/(T*L))*n := by
  have hd (i : ℕ) (hi : i < p/2) : denom p i ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    change ((↑(2*i+1) : ZMod p).val) = (0 : ZMod p).val at hh
    rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by omega)] at hh
    omega
  have htwo : (2 : ZMod p) ≠ 0 := (ThetaFourier.two_unit hp).ne_zero
  let c := denom p k / 2
  let x := fun j => c / denom p (a+j)
  have hc : c ≠ 0 := div_ne_zero (hd k hk) htwo
  have hx (j : ℕ) (hj : j < n) : x j ≠ 0 := div_ne_zero hc (hd _ (by omega))
  have hex (t : ZMod p) (ht : t ≠ 0) (hn : near T t) : ‖expSum x n t‖ ≤ E := by
    have h := he t ht hn
    simpa only [expSum, x, c, div_mul_eq_mul_div] using h
  have hsign (j : ℕ) : sgn p (a+j) k =
      (if (2*x j).val % 2 = 1 then (1:ℝ) else -1) := by
    have hv : 2*x j = denom p k / denom p (a+j) := by
      dsimp [x,c]
      rw [← mul_div_assoc, mul_div_cancel₀ _ htwo]
    simp only [hv, sgn, quotientSign, denom, Int.cast_ite, Int.cast_one, Int.cast_neg]
  simp_rw [hsign]
  exact signed hp x hx hL hLp hH hHm hT hTm hE hex

#print axioms block
end
end Arxiv.«2501.03234».ThetaShortParity
