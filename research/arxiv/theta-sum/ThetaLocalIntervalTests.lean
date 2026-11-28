import ThetaLocalWeightedLimits

/-! Finite inequalities converting a continuous tent test into counts of
residual values in a prescribed open interval and arithmetic progression. -/
namespace Arxiv.«2501.03234».ThetaLocalIntervalTests
open Real Filter Finset ThetaCharacterPrimeMeans ThetaIdentityFiber
open scoped NNReal
noncomputable section

def cell (q r : ℕ) (s : Finset ℕ) := s.filter (fun n => n%q=r)
def hits (q r : ℕ) (y d : ℝ) (s : Finset ℕ) := (cell q r s).filter (fun n => |residual n-y|<d)
def tent (y d x : ℝ) := max 0 (d-|x-y|)
def test (q r : ℕ) (y d τ : ℝ) (n : ℕ) := selectClass r q n*(tent y d (residual n)-d*(1-2*τ))

theorem lip (y d c : ℝ) : LipschitzWith 1 (fun x => tent y d x-c) := by
  apply LipschitzWith.of_dist_le_mul; intro x z
  simp only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right,tent]
  have hh := abs_sub_abs_le_abs_sub (x-y) (z-y)
  rw [sub_sub_sub_cancel_right] at hh
  have hl := abs_sub_abs_le_abs_sub (z-y) (x-y)
  rw [sub_sub_sub_cancel_right,abs_sub_comm z x] at hl
  apply abs_le.mpr
  constructor <;> rw [max_def,max_def] <;> split_ifs <;> linarith [abs_nonneg (x-z)]

private theorem sum_test (q r : ℕ) (y d τ : ℝ) (s : Finset ℕ) :
    (∑ n∈s,test q r y d τ n)=(∑ n∈cell q r s,tent y d (residual n))-d*(1-2*τ)*(cell q r s).card := by
  calc _ = ∑ n∈cell q r s,(tent y d (residual n)-d*(1-2*τ)) := by
           rw [cell,sum_filter];apply sum_congr rfl;intro n _
           by_cases h : n%q=r <;> simp [test,selectClass,h]
       _ = _ := by rw [sum_sub_distrib,sum_const,nsmul_eq_mul];ring

theorem lower (q r : ℕ) (y : ℝ) {d τ : ℝ} (hd : 0<d) (ht₁ : τ≤1) (s : Finset ℕ)
    (h : (1-τ)*(cell q r s).card≤((hits q r y (d*τ) s).card:ℝ)) :
    0≤∑ n∈s,test q r y d τ n := by
  let b := d*(1-τ)
  have hb : 0≤b := mul_nonneg hd.le (sub_nonneg.mpr ht₁)
  let G := hits q r y (d*τ) s
  have H : (G.card:ℝ)*b≤∑ n∈cell q r s,tent y d (residual n) := calc
    _ = ∑ _n∈G,b := by simp
    _ ≤ ∑ n∈G,tent y d (residual n) := sum_le_sum fun n hn => by
      have hh := (mem_filter.mp hn).2
      change |residual n-y|<d*τ at hh
      exact (show b≤d-|residual n-y| by dsimp [b];linarith only [hh]).trans (le_max_right ..)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => le_max_left ..)
  rw [sum_test]
  have hcost := mul_le_mul_of_nonneg_right h hb
  change (1-τ)*((cell q r s).card:ℝ)*b≤(G.card:ℝ)*b at hcost
  dsimp only [b] at hcost H
  nlinarith only [hcost,H,mul_nonneg (mul_nonneg hd.le (sq_nonneg τ)) (Nat.cast_nonneg (cell q r s).card (α:=ℝ))]

theorem upper (q r : ℕ) (y : ℝ) {d : ℝ} (hd : 0<d) (τ : ℝ) (s : Finset ℕ) :
    (∑ n∈s,test q r y d τ n)≤d*(hits q r y d s).card-d*(1-2*τ)*(cell q r s).card := by
  rw [sum_test,sub_le_sub_iff_right]
  have H : (∑ n∈cell q r s,tent y d (residual n))≤
      ∑ n∈cell q r s,if |residual n-y|<d then d else 0 := by
    apply sum_le_sum;intro n _
    by_cases h : |residual n-y|<d
    · rw [if_pos h];exact max_le hd.le (by linarith only [abs_nonneg (residual n-y)])
    · rw [if_neg h];exact max_le le_rfl (sub_nonpos.mpr (le_of_not_gt h))
  apply H.trans_eq
  rw [←sum_filter,sum_const,nsmul_eq_mul];exact mul_comm ..

#print axioms lower
#print axioms upper
end
end Arxiv.«2501.03234».ThetaLocalIntervalTests
