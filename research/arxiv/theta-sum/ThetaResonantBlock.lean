import ThetaDyadicDiscrepancy
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A prime with a small theta sum has a large cotangent block above the short initial range. -/
namespace Arxiv.«2501.03234».ThetaResonantBlock
open Finset Real ThetaShortReciprocalBlocks ThetaDyadicDiscrepancy ThetaCotangentTriangle
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def stop (p i : ℕ) := min (p/2) (2^(i+1))
def tile (p i : ℕ) [Fact p.Prime] := block p (2^i) (stop p i)

theorem lower_eq (hp : p%2=1) : lowerTriangle p=block p 0 (p/2) := by
  unfold lowerTriangle block
  rw [Nat.Ico_zero_eq_range]
  congr 1
  apply sum_congr rfl
  intro j hj
  congr 1
  apply sum_congr rfl
  intro k hk
  have hj' := mem_range.mp hj
  have hk' := mem_range.mp hk
  rw [sgn, quotient_eq_reciprocal hp (by omega) (by omega) (by omega) (by omega)]
  rfl

theorem small_sum_forces_triangle (hp : p%2=1) (h₃₆ : 36 ≤ p)
    (hS : (S p:ℝ) ≤ (p:ℝ)*log p/100) :
    (p:ℝ)*(Nat.log 2 p:ℕ)/256 ≤ |block p 0 (p/2)| := by
  let t := Nat.log 2 p
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have he := Nat.pow_log_le_self 2 (by omega : p≠0)
  have ht := log_le_log (show 0<(2:ℝ)^t by positivity) (show (2:ℝ)^t ≤ p by exact_mod_cast he)
  rw [log_pow] at ht
  have hl : (t:ℝ)/2 ≤ log p := by
    have h := mul_le_mul_of_nonneg_left (show (1:ℝ)/2 ≤ log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg t)
    linarith
  have h₆ : 2*log 6 ≤ log (p:ℝ) := by
    have h := log_le_log (show 0<(6:ℝ)^2 by positivity) (show (6:ℝ)^2 ≤ p by exact_mod_cast h₃₆)
    simpa only [log_pow,Nat.cast_ofNat] using h
  have hh := S_sub_lowerTriangle_log hp
  rw [lower_eq hp,log_div hx.ne' (by norm_num)] at hh
  have hπ : (3:ℝ)/64 ≤ 3/(4*Real.pi^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2]
  have hlog := log_nonneg (show 1 ≤ (p:ℝ) by exact_mod_cast (show 1 ≤ p by omega))
  have hmain : (3:ℝ)/64*(p:ℝ)*(log p/2) ≤ (S p:ℝ)-block p 0 (p/2) := by
    apply le_trans _ hh
    gcongr; linarith
  have hblock := neg_le_abs (block p 0 (p/2))
  change (p:ℝ)*t/256 ≤ _
  nlinarith only [hmain,hS,hblock,mul_le_mul_of_nonneg_left hl hx.le, mul_nonneg hx.le hlog]

/-- Passing through a block costs a factor proportional to its dyadic level. -/
theorem tile_bound {i : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (H : ∀ k<stop p i,∀ a,2^i ≤ a → a ≤ stop p i →
      ∀ n ≤ stop p i-a, |∑ j∈range n, sgn p (a+j) k| ≤ D) :
    |tile p i| ≤ 4*(p:ℝ)*((i:ℝ)+1)*D/(2:ℝ)^i := by
  let N := stop p i
  have hN : N ≤ p/2 := min_le_left ..
  have hpos : 0<N := lt_min (Nat.div_pos (Fact.out : p.Prime).two_le (by decide)) (by positivity)
  have hNc : (N:ℝ) ≤ (2:ℝ)^(i+1) := by exact_mod_cast min_le_right (p/2) (2^(i+1))
  have hl := log_le_log (Nat.cast_pos.mpr hpos) hNc
  rw [log_pow,Nat.cast_succ] at hl
  have hh : (harmonic N:ℝ) ≤ 2*((i:ℝ)+1) := by
    have hlog : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [harmonic_le_one_add_log N,hl,
      mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (i:ℝ)+1),Nat.cast_nonneg (α:=ℝ) i]
  apply (block_bound (p:=p) (J:=2^i) hN hD H).trans
  apply div_le_div₀ _ _ (by positivity) _
  · positivity
  · nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg p)) hD]
  · push_cast; linarith [show 0 ≤ (2:ℝ)^i by positivity]

lemma trivial_tile (i : ℕ) : |tile p i| ≤ 8*(p:ℝ)*((i:ℝ)+1) := by
  have h := tile_bound (p:=p) (i:=i) (show 0 ≤ 2*(2:ℝ)^i by positivity) (by
    intro k hk a ha ha' n hn
    have hn' : n ≤ 2^(i+1) := by change n ≤ min (p/2) (2^(i+1))-a at hn; exact (Nat.le_trans hn ((Nat.sub_le ..).trans (min_le_right ..)))
    apply (abs_sum_le_sum_abs ..).trans
    have one (j) : |sgn p (a+j) k|=1 := by dsimp [sgn,quotientSign]; split_ifs <;> norm_num
    simp only [one,sum_const,card_range,nsmul_eq_mul,mul_one]
    exact_mod_cast (show n ≤ 2*2^i by rw [pow_succ] at hn';omega))
  apply h.trans_eq
  field_simp
  ring

theorem large_tile {s t : ℕ} (ht : p/2 ≤ 2^t) (hs : s ≤ t)
    (hsmall : 8192*s^2 ≤ t) (htpos : 0<t)
    (hbad : (p:ℝ)*t/256 ≤ |block p 0 (p/2)|) :
    ∃ i, s ≤ i ∧ i<t ∧ (p:ℝ)/1024 < |tile p i| := by
  classical
  by_contra! h
  have he := tiled (p:=p) (p/2) t
  rw [min_eq_left ht] at he
  change (∑ i∈range t,tile p i)=_ at he
  rw [←he] at hbad
  have hsum := hbad.trans (abs_sum_le_sum_abs ..)
  rw [←sum_range_add_sum_Ico (fun i => |tile p i|) hs] at hsum
  have hlow : ∑ i∈range s,|tile p i| ≤ 8*(p:ℝ)*(s:ℝ)^2 := by
    calc
      _ ≤ ∑ _i∈range s,8*(p:ℝ)*s := by
        apply sum_le_sum; intro i hi
        apply (trivial_tile i).trans
        gcongr
        exact_mod_cast mem_range.mp hi
      _ = _ := by simp; ring
  have hhi : ∑ i∈Ico s t,|tile p i| ≤ (t:ℝ)*((p:ℝ)/1024) := by
    apply (sum_le_sum (fun i hi => h i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2)).trans
    simp only [sum_const,nsmul_eq_mul,Nat.card_Ico]
    gcongr
    exact Nat.sub_le ..
  have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have ht₀ : 0<(t:ℝ) := by exact_mod_cast htpos
  have hs' : 8192*(s:ℝ)^2 ≤ t := by exact_mod_cast hsmall
  nlinarith only [hsum,hlow,hhi,mul_le_mul_of_nonneg_left hs' hp₀.le,mul_pos hp₀ ht₀]

#print axioms small_sum_forces_triangle
#print axioms large_tile
end
end Arxiv.«2501.03234».ThetaResonantBlock
