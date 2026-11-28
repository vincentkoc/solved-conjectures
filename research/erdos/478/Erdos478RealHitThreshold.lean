import Erdos478DiverseLengthTails

/-! # Real thresholds in the factorial hit-length law -/

namespace Erdos478.ConditionalGaps
open FrobeniusCounts BinaryGap Finset
open scoped Classical
noncomputable section

theorem real_tilted_upper (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    {b z : ℝ} (hb : 0≤b) (hz : 0<z) (hz₁ : z≤1) :
    law s (fun u => (u.card : ℝ)<b)≤Real.exp (s.card*Real.log ((1+z)/2)-b*Real.log z) := by
  let n := ⌊b⌋₊
  have cut : law s (fun u => (u.card : ℝ)<b)≤law s (fun u => u.card≤n) := by
    apply uniform_mono
    intro g
    let u := hits (CommonField s) s g
    change (if (u.card : ℝ)<b then (1:ℝ) else 0)≤(@ite ℝ (u.card≤n) (Classical.propDecidable _) 1 0)
    by_cases h : (u.card : ℝ)<b
    · simp [h,(Nat.le_floor_iff hb).mpr h.le,n]
    · by_cases h' : u.card≤n <;> simp [h,h']
  have basepos : 0<(1+z)/2 := by positivity
  have exp_pow (x : ℝ) (hx : 0<x) (d : ℕ) : x^d=Real.exp ((d:ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  apply le_trans (cut.trans (tilted_upper s good n hz hz₁))
  rw [exp_pow _ basepos, exp_pow z hz,← Real.exp_sub]
  exact Real.exp_le_exp.mpr (sub_le_sub_left (mul_le_mul_of_nonpos_right
    (Nat.floor_le hb) (Real.log_nonpos hz.le hz₁)) _)

theorem complementary_threshold (s : Finset Nat.Primes) (b : ℝ) :
    law s (fun u => b≤(u.card:ℝ))=1-law s (fun u => (u.card:ℝ)<b) := by
  let f (g : Aut (CommonField s)) : ℝ := if ((hits (CommonField s) s g).card:ℝ)<b then 1 else 0
  have he : (fun g => if b≤((hits (CommonField s) s g).card:ℝ) then (1:ℝ) else 0)=(fun _ => 1)-f := by
    funext g
    by_cases h : b≤((hits (CommonField s) s g).card:ℝ)
    · simp [f,h,not_lt.mpr h]
    · simp [f,h,lt_of_not_ge h]
  change uniform _ _=1-uniform _ f
  rw [he,map_sub,uniform_one]

#print axioms real_tilted_upper
#print axioms complementary_threshold
end
end Erdos478.ConditionalGaps
