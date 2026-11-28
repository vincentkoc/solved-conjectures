import ThetaSmoothedHalf
import ThetaShortReciprocalBlocks

/-! The parity of a nonzero field quotient is a half-interval test. -/

namespace Arxiv.«2501.03234».ThetaReciprocalParity
open Finset ThetaSmoothedHalf ThetaShortReciprocalBlocks ThetaCotangentTriangle
variable {p : ℕ} [Fact p.Prime]

lemma twice_odd (hp : p % 2 = 1) (x : ZMod p) :
    (2*x).val % 2 = 1 ↔ p/2 < x.val := by
  rw [two_mul, ZMod.val_add]
  have hx := x.val_lt
  by_cases h : x.val + x.val < p
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (show p ≤ x.val+x.val by omega),
      Nat.mod_eq_of_lt (show x.val+x.val-p < p by omega)]
    omega

lemma hits_complement (hp : p % 2 = 1) (x : ℕ → ZMod p) {n : ℕ}
    (hx : ∀ j < n, x j ≠ 0) :
    hits x n (p/2+1) + hits (fun j => -x j) n (p/2+1) = n := by
  unfold hits
  rw [← sum_add_distrib]
  calc
    _ = ∑ j ∈ range n, 1 := by
      apply sum_congr rfl
      intro j hj
      have h := hx j (mem_range.mp hj)
      have : NeZero (x j) := ⟨h⟩
      rw [ZMod.val_neg_of_ne_zero]
      have := (x j).val_lt
      split_ifs <;> omega
    _ = _ := by simp

theorem signed_half (hp : p % 2 = 1) (x : ℕ → ZMod p) {n L H : ℕ}
    (hx : ∀ j < n, x j ≠ 0) (hL : 0 < L) (hLp : p/2+L ≤ p)
    (hH : 0 < H) (hHm : H ≤ p/2) {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ t : ZMod p, t ≠ 0 → ‖expSum x n t‖ ≤ E) :
    |∑ j ∈ range n, (if (2*x j).val % 2 = 1 then (1:ℝ) else -1)| ≤
      2*(n:ℝ)*L/p + 4*((harmonic H : ℝ)+(p:ℝ)/(H*L))*E := by
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
  have hen (t : ZMod p) (ht : t ≠ 0) :
      ‖expSum (fun j => -x j) n t‖ ≤ E := by
    simpa [expSum, neg_mul, mul_neg] using he (-t) (neg_ne_zero.mpr ht)
  have h₁ := half_upper x hp hL hLp hH hHm hE he
  have h₂ := half_upper (fun j => -x j) hp hL hLp hH hHm hE hen
  have hc := hits_complement hp x hx
  have hc' : (hits x n (p/2+1) : ℝ) + hits (fun j => -x j) n (p/2+1) = n := by exact_mod_cast hc
  rw [hsum, abs_le]
  constructor <;> linarith

def denom (p j : ℕ) : ZMod p := (2*j+1 : ℕ)

theorem block_signs (hp : p % 2 = 1) {a n k L H : ℕ} (hk : k < p/2) (han : a+n ≤ p/2)
    (hL : 0 < L) (hLp : p/2+L ≤ p) (hH : 0 < H) (hHm : H ≤ p/2)
    {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ c : ZMod p, c ≠ 0 →
      ‖∑ j ∈ range n, ZMod.stdAddChar (c / denom p (a+j))‖ ≤ E) :
    |∑ j ∈ range n, sgn p (a+j) k| ≤
      2*(n:ℝ)*L/p + 4*((harmonic H : ℝ)+(p:ℝ)/(H*L))*E := by
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
  have hex (t : ZMod p) (ht : t ≠ 0) : ‖expSum x n t‖ ≤ E := by
    have h := he (c*t) (mul_ne_zero hc ht)
    simpa only [expSum, x, div_mul_eq_mul_div] using h
  have hsign (j : ℕ) : sgn p (a+j) k =
      (if (2*x j).val % 2 = 1 then (1:ℝ) else -1) := by
    have hv : 2*x j = denom p k / denom p (a+j) := by
      dsimp [x,c]
      rw [← mul_div_assoc, mul_div_cancel₀ _ htwo]
    simp only [hv, sgn, quotientSign, denom, Int.cast_ite, Int.cast_one, Int.cast_neg]
  simp_rw [hsign]
  exact signed_half hp x hx hL hLp hH hHm hE hex

#print axioms block_signs
end Arxiv.«2501.03234».ThetaReciprocalParity
