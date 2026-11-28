import Erdos478ConditionalHitPowers

/-! # An exponential bound relative to the mass of an earlier count event -/

namespace Erdos478.FirstCollision
open Polynomial Finset BinaryGap FrobeniusCounts
open scoped Classical
noncomputable section

theorem weighted_threshold (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [Normal ℚ K]
    (b : Finset ℕ) (bp : ∀ k∈b, 0<k) (s : Finset Nat.Primes)
    (below : ∀ k∈b, ∀ i∈s, k < i.val) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    (split : ∀ k∈combined b s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (W : (b → ℕ) → ℝ) (hn : ∀ a, 0≤W a) (θ : ℝ) {z : ℝ} (hz : 0<z) (hz' : z≤1) :
    let w (g : Aut K) := W (fun i => fixedGap K i.val g)
    (1-Real.exp (s.card*Real.log ((1+z)/2)-θ*Real.log z))*uniform (Aut K) w ≤
      uniform (Aut K) (fun g => if θ≤((ConditionalGaps.hits K s g).card:ℝ) then w g else 0) := by
  let w (g : Aut K) := W (fun i => fixedGap K i.val g)
  let m (g : Aut K) := (ConditionalGaps.hits K s g).card
  let u (g : Aut K) := w g*z^m g
  let h (g : Aut K) := if θ≤(m g : ℝ) then w g else 0
  let t := Real.exp (θ*Real.log z)
  have pos : 0<t := Real.exp_pos _
  have le : ∀ g, (t • (w-h)) g≤u g := by
    intro g
    simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,h,u]
    split_ifs with he
    · simpa only [sub_self,mul_zero] using mul_nonneg (hn _) (pow_nonneg hz.le (m g))
    · have ht : t≤z^m g := by
        rw [show z^m g=Real.exp ((m g:ℝ)*Real.log z) by rw [Real.exp_nat_mul,Real.exp_log hz]]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (le_of_not_ge he) (Real.log_nonpos hz.le hz'))
      rw [sub_zero,mul_comm]
      exact mul_le_mul_of_nonneg_left ht (hn _)
  have bound := (uniform_mono le).trans (weighted_power K b bp s below good split W hn hz.le hz')
  rw [map_smul,map_sub,smul_eq_mul] at bound
  have qpos : 0<(1+z)/2 := by positivity
  have factor : Real.exp (s.card*Real.log ((1+z)/2)-θ*Real.log z)=((1+z)/2)^s.card/t := by
    rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log qpos]
  rw [factor]
  change (1-((1+z)/2)^s.card/t)*uniform (Aut K) w≤uniform (Aut K) h
  have diff : uniform (Aut K) w-uniform (Aut K) h≤uniform (Aut K) w*((1+z)/2)^s.card/t :=
    (le_div_iff₀ pos).mpr (by linarith only [bound,mul_comm t (uniform (Aut K) w-uniform (Aut K) h)])
  rw [mul_div_assoc] at diff
  linarith

#print axioms weighted_threshold
end
end Erdos478.FirstCollision
