import Erdos478QuadraticGapMajorant
import Erdos478FrobeniusBandVariance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # A one-sided Gaussian tail for distinct repeated factorial endpoints -/

namespace Erdos478.GapTail
open Finset Filter Topology GapVariance RootMoments BinaryGap GapBands GapSieve GapDensity
open scoped Classical
noncomputable section

private theorem chernoff (δ : ℝ) (m : ℕ) :
    Real.exp (δ*((1-δ)*m))*(base (Real.exp (-δ)))^m ≤ Real.exp (-δ^2*m/2) := by
  have ident : Real.exp (δ*(1-δ))*base (Real.exp (-δ))=Real.exp (-δ^2)*Real.cosh δ := by
    rw [show δ*(1-δ) = -δ^2+δ by ring,Real.exp_add,Real.cosh_eq,base]
    simp only [Real.exp_neg]
    field_simp
  have single : Real.exp (δ*(1-δ))*base (Real.exp (-δ))≤Real.exp (-δ^2/2) := by
    rw [ident,show -δ^2/2= -δ^2+δ^2/2 by ring,Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq δ) (Real.exp_pos _).le
  rw [show δ*((1-δ)*m)=(m:ℝ)*(δ*(1-δ)) by ring,Real.exp_nat_mul,← mul_pow,
    show -δ^2*m/2=(m:ℝ)*(-δ^2/2) by ring,Real.exp_nat_mul]
  apply pow_le_pow_left₀ _ single
  unfold base
  positivity

/-- For each fixed family of m lengths, the upper natural prime density
of a relative shortfall δ is at most exp(-δ²m/2). -/
theorem finite_lower_tail (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    (good : ∀ i∈s, broad i.val ∧ 3 < i.val) {δ ε : ℝ} (hd : 0≤δ) (heps : 0<ε) :
    ∀ᶠ X in atTop, fraction X (fun p => ((joined s p).card:ℝ)<(1-δ)*s.card) <
      Real.exp (-δ^2*s.card/2)+ε := by
  let A := countingAverage pit
  let z := Real.exp (-δ)
  let M := Real.exp (δ*((1-δ)*s.card))
  have hz : 0<z := Real.exp_pos _
  have hz' : z≤1 := Real.exp_le_one_iff.mpr (by linarith)
  let w (p : ℕ) := ∏ i∈s, major z (observation i p)
  obtain ⟨B,hB⟩ := eventual_endpoint_sum s
  let cap (p : ℕ) := if B<p then M*w p else 1
  have hm := (major_product_mean z A s good).const_mul M
  have hm' : Tendsto (fun X => A.avg X (M • w)) atTop (𝓝 (M*(base z)^s.card)) := by
    simpa only [map_smul,smul_eq_mul] using hm
  have hc := A.finite_change (a:=cap) (b:=M • w) B (fun p h _ => if_pos h)
  have lim := hc.add hm'
  simp only [sub_add_cancel,zero_add] at lim
  let bad (p : ℕ) := ((joined s p).card:ℝ)<(1-δ)*s.card
  let ind (p : ℕ) := if bad p then (1:ℝ) else 0
  have bound (p : ℕ) (hp : p.Prime) : ind p≤cap p := by
    by_cases h : B<p
    · rw [show cap p=M*w p from if_pos h]
      have low := pow_sum_le_product hz.le hz' s p
      apply le_trans _ (mul_le_mul_of_nonneg_left low (Real.exp_pos _).le)
      by_cases hb : bad p
      · rw [show ind p=1 from if_pos hb]
        have eq : ((joined s p).card:ℝ)=((∑ i∈s, count i p : ℕ):ℝ) := by
          rw [Nat.cast_sum]
          exact hB p h hp
        change ((joined s p).card:ℝ)<_ at hb
        rw [eq] at hb
        rw [show M*z^(∑ i∈s, count i p)=Real.exp (δ*((1-δ)*s.card)+(∑ i∈s, count i p : ℕ)*(-δ)) by
          rw [Real.exp_add,Real.exp_nat_mul]]
        apply Real.one_le_exp_iff.mpr
        nlinarith [mul_nonneg hd (sub_nonneg.mpr hb.le)]
      · rw [show ind p=0 from if_neg hb]
        exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hz.le _)
    · simp only [cap,if_neg h,ind]
      split_ifs <;> norm_num
  filter_upwards [lim.eventually_lt_const (lt_of_le_of_lt (chernoff δ s.card)
    (lt_add_of_pos_right _ heps))] with X hx
  have h := (A.mono X bound).trans_lt hx
  change ordinary X ind<_ at h
  simpa only [ind,bad,ordinary_eq] using h

#print axioms finite_lower_tail
end
end Erdos478.GapTail
