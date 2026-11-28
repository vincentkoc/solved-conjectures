import Erdos478RealHitThreshold
import Erdos478FrobeniusBandVariance

/-! # Exponential bounds for distinct collision lengths in proportional windows

In a proportional interval the number of eligible lengths is asymptotic to
((L-1)/3) K/log K. A fixed tilt gives an exponential upper bound for the
exceptional proportion of prime moduli.
-/

namespace Erdos478.ConditionalGaps
open Finset Filter Topology FrobeniusBands BandWeights BinaryGap GapDensity GapSieve
open scoped Classical
noncomputable section

/-- The dyadic or proportional length count converts the finite Chernoff exponent
to an eventual strict logarithmic rate. -/
theorem window_exponent (input : countingInput broad (1/3))
    {H : ℕ → ℕ} {L b z A : ℝ} (hL : 1<L) (hw : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hA : A<b*Real.log z-(L-1)/3*Real.log ((1+z)/2)) :
    ∀ᶠ K : ℕ in atTop, ((family K (H K)).card:ℝ)*Real.log ((1+z)/2)-(b*K/Real.log K)*Real.log z
      < -A*K/Real.log K := by
  let c := (L-1)/3
  let m (K : ℕ) : ℝ := (family K (H K)).card
  let w := Proportional.scale
  let q := Real.log ((1+z)/2)
  have mass : Tendsto (fun K => m K*w K) atTop (𝓝 c) := by
    rw [show c=(1/3)*(L-1) by dsimp [c]; ring]
    simpa only [m,w,family_card,Proportional.scale,mul_div_assoc] using length_asymptotic input hL hw
  have rate := (tendsto_const_nhds (x:=b*Real.log z)).sub (mass.mul_const q)
  filter_upwards [rate.eventually_const_lt hA,eventually_ge_atTop 3] with K hrate hK
  have kp : 0<(K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have lp : 0<Real.log K := Real.log_pos (by exact_mod_cast (show 1<K by omega))
  have wp : 0<w K := div_pos lp kp
  have factor (x : ℝ) : x/w K=x*K/Real.log K := by
    dsimp [w,Proportional.scale]
    field_simp
  let θ := b/w K
  have exp_lt : m K*q-θ*Real.log z < -A/w K := by
    apply (lt_div_iff₀ wp).mpr
    have eq : (m K*q-θ*Real.log z)*w K=m K*w K*q-b*Real.log z := by
      dsimp [θ]; field_simp
    rw [eq]
    change A<b*Real.log z-m K*w K*q at hrate
    linarith
  simpa only [θ,factor] using exp_lt

/-- For any tilt in (0,1), all exponents strictly below the displayed
logarithmic rate are valid. The inner prime cutoff depends on K. -/
theorem window_of_inputs (pit : DegreeOnePrimeIdealTheorem) (input : countingInput broad (1/3))
    {H : ℕ → ℕ} {L b z A : ℝ} (hL : 1<L) (hw : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hb : 0≤b) (hz : 0<z) (hz₁ : z<1) (hA : A<b*Real.log z-(L-1)/3*Real.log ((1+z)/2)) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, 1-Real.exp (-A*K/Real.log K)<fraction X (fun p =>
      let U := GapSieve.hits (family K (H K)) p
      b*K/Real.log K≤(U.card:ℝ) ∧ ((Ico 1 p).image (fun i => i.factorial%p)).card+U.card≤p-1) := by
  filter_upwards [window_exponent input hL hw hA,eventually_ge_atTop 3] with K exp_lt hK
  let s := family K (H K)
  let θ := b*K/Real.log K
  have good (i) (hi : i∈s) : broad i.val ∧ 3 < i.val := by
    obtain ⟨lo,_,hi⟩ := family_mem.mp hi
    exact ⟨hi,by omega⟩
  have bad := real_tilted_upper s good (b:=θ) (div_nonneg (mul_nonneg hb (Nat.cast_nonneg _))
    (Real.log_nonneg (by exact_mod_cast (show 1≤K by omega)))) hz hz₁.le
  have strict := bad.trans_lt (Real.exp_lt_exp.mpr exp_lt)
  have lower : 1-Real.exp (-A*K/Real.log K)<law s (fun u => θ≤(u.card:ℝ)) := by
    rw [complementary_threshold]
    linarith
  have lim := certified_of_pit pit s (fun u => θ≤(u.card:ℝ))
  exact lim.eventually_const_lt lower

#print axioms window_exponent
#print axioms window_of_inputs
end
end Erdos478.ConditionalGaps
