import Erdos478NormalizedWindowEnergy

/-! # Factorial window statistics for growing spans on the host prime filter -/

namespace Erdos478.WindowAverage
open Finset Filter Topology
open scoped Classical
noncomputable section

abbrev alongPrimes : Filter ℕ := atTop ⊓ principal {p : ℕ | p.Prime}

theorem eventually_prime : ∀ᶠ p in alongPrimes, p.Prime :=
  (eventually_principal.mpr (fun _ hp => hp)).filter_mono inf_le_right

private theorem smaller_ratio (H : ℕ → ℕ) {k : ℕ} (hk : 0<k)
    (small : Tendsto (fun p => (H p:ℝ)^k/p) alongPrimes (𝓝 0)) :
    Tendsto (fun p => (H p:ℝ)/p) alongPrimes (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun p => by positivity) _ small
  exact Eventually.of_forall fun p => div_le_div_of_nonneg_right
    (by exact_mod_cast (Nat.le_pow (a:=H p) hk)) (by positivity)

theorem starts_asymptotic (H : ℕ → ℕ)
    (small : Tendsto (fun p => (H p:ℝ)/p) alongPrimes (𝓝 0)) :
    (∀ᶠ p in alongPrimes, H p+1<p) ∧
    Tendsto (fun p => ((starts p (H p)).card:ℝ)/p) alongPrimes (𝓝 1) := by
  have reciprocal := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).mono_left (show alongPrimes≤atTop from inf_le_left)
  have gone : Tendsto (fun p : ℕ => ((H p:ℝ)+1)/p) alongPrimes (𝓝 0) := by
    simpa [add_div] using small.add reciprocal
  have fits : ∀ᶠ p in alongPrimes, H p+1<p := by
    filter_upwards [gone.eventually_lt_const (by norm_num : (0:ℝ)<1),eventually_prime] with p h hp
    have pos : (0:ℝ)<p := by exact_mod_cast hp.pos
    have low := (div_lt_iff₀ pos).mp h
    exact_mod_cast (by simpa using low : (H p:ℝ)+1<(p:ℝ))
  refine ⟨fits,?_⟩
  have lim : Tendsto (fun p : ℕ => 1-((H p:ℝ)+1)/p) alongPrimes (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub gone
  apply lim.congr'
  filter_upwards [fits,eventually_prime] with p h hp
  have eq : (starts p (H p)).card+(H p+1)=p := by rw [starts_card]; omega
  have real : ((starts p (H p)).card:ℝ)+((H p:ℝ)+1)=p := by exact_mod_cast eq
  field_simp [show (p:ℝ)≠0 by exact_mod_cast hp.ne_zero]
  linarith

/-- At sub-cube-root spans, almost every positive window has all its values distinct. -/
theorem subcubic_injective (H : ℕ → ℕ)
    (small : Tendsto (fun p => (H p:ℝ)^3/p) alongPrimes (𝓝 0)) :
    Tendsto (fun p => exceptionalFraction p (H p) 1) alongPrimes (𝓝 0) := by
  obtain ⟨_,den⟩ := starts_asymptotic H (smaller_ratio H (by decide : 0<3) small)
  have lim := small.div den (by norm_num : (1:ℝ)≠0)
  apply squeeze_zero' (Eventually.of_forall fun p => by unfold exceptionalFraction; positivity) _ (by simpa using lim)
  filter_upwards [eventually_prime] with p hp
  have bound (h : ℕ) : ((exceptionalStarts p h 1).card:ℝ)≤(h:ℝ)^3 := by
    cases h with
    | zero =>
      have raw := normalized_exception hp 0 1
      push_cast at raw ⊢
      linarith
    | succ v =>
      have raw := normalized_exception hp (v+1) 1
      push_cast at raw ⊢
      nlinarith [show (0:ℝ)≤v by positivity,sq_nonneg (v:ℝ),show (0:ℝ)≤(v:ℝ)^3 by positivity]
  change _ ≤ ((H p:ℝ)^3/p)/(((starts p (H p)).card:ℝ)/p)
  rw [div_div_div_cancel_right₀ (by exact_mod_cast hp.ne_zero : (p:ℝ)≠0)]
  exact div_le_div_of_nonneg_right (bound _) (by positivity)

/-- Below the square-root scale, the fraction of windows losing a fixed
positive proportion of their values tends to zero. -/
theorem subsquare_relative_loss (H : ℕ → ℕ) (ε : ℝ) (pos : 0<ε)
    (small : Tendsto (fun p => (H p:ℝ)^2/p) alongPrimes (𝓝 0)) :
    Tendsto (fun p => exceptionalFraction p (H p) ⌈ε*(H p+1)⌉₊) alongPrimes (𝓝 0) := by
  have low := smaller_ratio H (by decide : 0<2) small
  obtain ⟨fits,den⟩ := starts_asymptotic H low
  have num : Tendsto (fun p : ℕ => (H p:ℝ)*(H p+2)/p) alongPrimes (𝓝 0) := by
    convert small.add ((tendsto_const_nhds (x:=(2:ℝ))).mul low) using 1
    · funext p; ring
    · norm_num
  have lim := (num.div den (by norm_num : (1:ℝ)≠0)).div_const (6*ε)
  apply squeeze_zero' (Eventually.of_forall fun p => by unfold exceptionalFraction; positivity) _ (by simpa using lim)
  filter_upwards [eventually_prime,fits] with p hp fit
  change _≤(((H p:ℝ)*(H p+2)/p)/(((starts p (H p)).card:ℝ)/p))/(6*ε)
  rw [div_div_div_cancel_right₀ (by exact_mod_cast hp.ne_zero : (p:ℝ)≠0)]
  have sp : 0<((starts p (H p)).card:ℝ) := by rw [starts_card]; exact_mod_cast (show 0<p-1-H p by omega)
  unfold exceptionalFraction
  field_simp
  linarith only [relative_loss_bound (H:=H p) hp ε]

#print axioms alongPrimes
#print axioms eventually_prime
#print axioms starts_asymptotic
#print axioms subcubic_injective
#print axioms subsquare_relative_loss
end
end Erdos478.WindowAverage
