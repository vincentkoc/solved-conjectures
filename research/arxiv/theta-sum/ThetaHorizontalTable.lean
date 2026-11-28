import ThetaHorizontalBox
import ThetaMeshObstruction

/-! Positive multipliers and the exact finite phase table for testing horizontal prefix sums. -/
namespace Arxiv.«2501.03234».ThetaHorizontalTable
open Finset Filter Real Asymptotics ThetaAdditiveReciprocity ThetaReciprocalMesh ThetaMeshObstruction
open scoped ComplexConjugate
noncomputable section

def radius (p : ℕ) (α : ℝ) := ⌊sqrt p*exp (-(log p)^α)⌋₊

/-- Row d represents denominator 4(d+1). Each positive multiplier uses the same rows
for all prefix lengths up to R. -/
def phases (R : ℕ) := (range R) ×ˢ (Icc 1 R)

theorem phase_card (R : ℕ) : (phases R).card=R^2 := by simp [phases,pow_two]

theorem term_budget (p : ℕ) (α : ℝ) :
    ((phases (radius p α)).card:ℝ) ≤ (p:ℝ)*exp (-2*(log p)^α) := by
  rw [phase_card,Nat.cast_pow]
  have h := Nat.floor_le (mul_nonneg (sqrt_nonneg (p:ℝ)) (exp_pos (-(log (p:ℝ))^α)).le)
  change (radius p α:ℝ)≤_ at h
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) h 2).trans_eq
  rw [mul_pow,sq_sqrt (Nat.cast_nonneg p),←exp_nat_mul]
  congr 2
  norm_num

theorem term_ratio {α : ℝ} (hα : 0<α) :
    Tendsto (fun p : ℕ => ((phases (radius p α)).card:ℝ)/p) atTop (nhds 0) := by
  have hu := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht := (tendsto_rpow_atTop hα).comp hu
  have hf := tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop (by norm_num : (0:ℝ)<2))
  apply squeeze_zero' (Eventually.of_forall (fun p => by positivity)) _ hf
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hpos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  apply (div_le_iff₀ hpos).mpr
  simpa only [Function.comp_apply,neg_mul,mul_comm] using term_budget p α

/-- Exact prefix update used when visiting the table once for each multiplier. -/
theorem update (p N : ℕ) (j : ℤ) :
    horizontal p (N+1) j=horizontal p N j+row p N j := by simp only [horizontal,sum_range_succ]

theorem prefix_change (p n k : ℕ) (j : ℤ) :
    ‖horizontal p (n+k) j-horizontal p n j‖≤k := by
  unfold horizontal
  rw [sum_range_add,add_sub_cancel_left]
  apply (norm_sum_le ..).trans
  simp [row]

theorem norm_natAbs (p N : ℕ) (j : ℤ) :
    ‖horizontal p N (j.natAbs:ℤ)‖=‖horizontal p N j‖ := by
  have hrow (d : ℕ) (k : ℤ) : row p d (-k)=conj (row p d k) := by
    let : NeZero (4*(d+1)) := ⟨by omega⟩
    unfold row
    push_cast
    rw [←AddChar.map_neg_eq_conj]
    congr 1
    ring
  have hneg (k : ℤ) : horizontal p N (-k)=conj (horizontal p N k) := by
    simp only [horizontal,hrow,map_sum]
  rcases le_or_gt 0 j with h|h
  · rw [Int.natCast_natAbs,abs_of_nonneg h]
  · rw [Int.natCast_natAbs,abs_of_neg h,hneg]
    exact Complex.norm_conj _

#print axioms phase_card
#print axioms term_budget
#print axioms term_ratio
#print axioms update
#print axioms norm_natAbs
end
end Arxiv.«2501.03234».ThetaHorizontalTable
