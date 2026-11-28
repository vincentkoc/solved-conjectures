import ThetaReciprocalParity
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Transfer initial reciprocal sums to intervals of odd denominators. -/

namespace Arxiv.«2501.03234».ThetaReciprocalPrefixes
open Finset Real ThetaReciprocalParity
variable {p : ℕ} [Fact p.Prime]

noncomputable def recipSum (N : ℕ) (c : ZMod p) : ℂ :=
  ∑ j ∈ range N, ZMod.stdAddChar (c / ((j+1 : ℕ) : ZMod p))

/-- The finite initial-sum estimate. Bourgain and Garaev give such a bound with
an absolute constant times log(p) (log log(p))³. -/
def PrefixBound (p : ℕ) [Fact p.Prime] (K : ℝ) : Prop :=
  ∀ (N : ℕ), 2 ≤ N → N < p → ∀ c : ZMod p, c ≠ 0 →
    ‖recipSum N c‖ ≤ K*N/(log N*sqrt (log N))

lemma odd_sum (T : ℕ) (c : ZMod p) :
    ∑ j ∈ range T, ZMod.stdAddChar (c / denom p j) = recipSum (2*T) c - recipSum T (c/2) := by
  induction T with
  | zero => simp [recipSum]
  | succ T ih =>
    simp only [Nat.mul_succ, sum_range_succ, ih]
    unfold recipSum
    rw [sum_range_succ (n:=2*T+1), sum_range_succ (n:=2*T), sum_range_succ (n:=T)]
    have h : (c/2)/((T+1 : ℕ) : ZMod p) = c/((2*T+1+1 : ℕ) : ZMod p) := by
      rw [div_div]
      congr 1
      push_cast
      ring
    rw [h]
    simp only [denom]
    abel

private lemma prefix_band {K : ℝ} (hK : 1 ≤ K) (hb : PrefixBound p K)
    {i N : ℕ} (h₁ : 2^i ≤ N) (h₂ : N ≤ 4*2^i) (h₃ : N < p) {c : ZMod p} (hc : c ≠ 0) :
    ‖recipSum N c‖ ≤ 32*K*(2:ℝ)^i/(((i:ℝ)+1)*sqrt ((i:ℝ)+1)) := by
  have hn : 0<N := lt_of_lt_of_le (by positivity) h₁
  by_cases hN : 2≤N
  · have hlog := log_le_log (show 0<(2:ℝ)^i by positivity) (show (2:ℝ)^i≤N by exact_mod_cast h₁)
    rw [log_pow] at hlog
    have hbase := log_le_log (show (0:ℝ)<2 by norm_num) (show (2:ℝ)≤N by exact_mod_cast hN)
    have htwo : (1:ℝ)/2 ≤ log 2 := by linarith [log_two_gt_d9]
    have hi : (i : ℝ)+1 ≤ 4*log N := by
      have := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg i)
      linarith
    have hlog₀ : 0<log (N : ℝ) := by linarith
    have hs := sqrt_le_sqrt hi
    rw [sqrt_mul (by norm_num : (0:ℝ)≤4), show sqrt (4:ℝ)=2 by norm_num] at hs
    have hd : ((i:ℝ)+1)*sqrt ((i:ℝ)+1) ≤ 8*(log N*sqrt (log N)) := by
      calc
        _ ≤ (4*log N)*(2*sqrt (log N)) :=
          mul_le_mul hi hs (sqrt_nonneg _) (by positivity)
        _ = _ := by ring
    have hnum : K*N ≤ 4*K*(2:ℝ)^i := by
      calc
        _ ≤ K*(4*(2:ℝ)^i) := by gcongr; exact_mod_cast h₂
        _ = _ := by ring
    apply (hb N hN h₃ c hc).trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (4*K*(2:ℝ)^i)*(8*(log N*sqrt (log N))) :=
        mul_le_mul hnum hd (by positivity) (by positivity)
      _ = _ := by ring
  · have he : N=1 := by omega
    subst N
    have hi : i=0 := by
      cases i with
      | zero => rfl
      | succ i => have hi : 0<2^i := by positivity
                  rw [pow_succ] at h₁
                  omega
    subst i
    simp [recipSum]
    linarith

theorem odd_interval {K : ℝ} (hK : 1≤K) (hb : PrefixBound p K) (hp : p%2=1)
    {i a n : ℕ} (ha : 2^i ≤ a) (han : a+n ≤ 2^(i+1)) (hm : a+n ≤ p/2)
    {c : ZMod p} (hc : c ≠ 0) :
    ‖∑ j ∈ range n, ZMod.stdAddChar (c / denom p (a+j))‖ ≤
      128*K*(2:ℝ)^i/(((i:ℝ)+1)*sqrt ((i:ℝ)+1)) := by
  let D := 32*K*(2:ℝ)^i/(((i:ℝ)+1)*sqrt ((i:ℝ)+1))
  have h₂ : (2 : ZMod p) ≠ 0 := (ThetaFourier.two_unit hp).ne_zero
  have htwo : 2^(i+1)=2^i*2 := pow_succ ..
  have hodd (T : ℕ) (lo : 2^i ≤ T) (hi : T ≤ a+n) :
      ‖∑ j ∈ range T, ZMod.stdAddChar (c / denom p j)‖ ≤ D+D := by
    rw [odd_sum]
    apply (norm_sub_le ..).trans
    apply add_le_add
    · exact prefix_band hK hb (by omega) (by omega) (by omega) hc
    · exact prefix_band hK hb lo (by omega) (by omega) (div_ne_zero hc h₂)
  have he := sum_range_add (fun j => ZMod.stdAddChar (c / denom p j)) a n
  have he' : (∑ j ∈ range n, ZMod.stdAddChar (c / denom p (a+j))) =
      (∑ j ∈ range (a+n), ZMod.stdAddChar (c / denom p j)) -
      ∑ j ∈ range a, ZMod.stdAddChar (c / denom p j) := by rw [he]; abel
  rw [he']
  apply (norm_sub_le ..).trans
  calc
    _ ≤ (D+D)+(D+D) := add_le_add (hodd (a+n) (by omega) le_rfl) (hodd a ha (by omega))
    _ = _ := by dsimp [D]; ring

#print axioms odd_interval
end Arxiv.«2501.03234».ThetaReciprocalPrefixes
