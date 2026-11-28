import CunninghamSingletonPairWindows

/-! Unconditional lower bounds for the averaged true two-stop count at growing gaps. -/

namespace CunninghamChain.GapWindow

open Finset Filter
open scoped Topology

private lemma normalized_lower {n h t v w : ℝ} (np : 0<n) (hp : 0<h) (vp : 0<v)
    (bd : (h*t)^2≤(n+h)*(h*t+2*w)) :
    (1+h/n)⁻¹*(t/v)^2-(n/(h*v))*(t/v) ≤ 2*n*w/(h^2*v^2) := by
  have nh : 0<n+h := by linarith
  have frac : 1+h/n=(n+h)/n := by field_simp
  rw [frac,inv_div]
  field_simp
  nlinarith only [bd]

/-- If the gap cutoff is smaller than the seed scale and larger than the
mean prime spacing, the triangularly weighted opposite-kind exact singleton
count has normalized lower limit at least one. -/
theorem mesoscopic_exact_pairs (H : ℕ → ℕ)
    (short : Tendsto (fun n : ℕ => (H n:ℝ)/n) atTop (𝓝 0))
    (many : Tendsto (fun n : ℕ => (H n:ℝ)*n.primeCounting/n) atTop atTop)
    {c : ℝ} (below : c<1) :
    ∀ᶠ n : ℕ in atTop, c < 2*(n:ℝ)*exactPairWeight n (H n)/((H n:ℝ)^2*(n.primeCounting:ℝ)^2) := by
  let t (n : ℕ) := ((bothSeeds n).card:ℝ)/n.primeCounting
  have tlim : Tendsto t atTop (𝓝 1) := both_proportion
  have ilim : Tendsto (fun n : ℕ => (1+(H n:ℝ)/n)⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x:=(1:ℝ))).add short).inv₀ (by norm_num)
  have zlim : Tendsto (fun n : ℕ => (n:ℝ)/((H n:ℝ)*n.primeCounting)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,inv_div] using tendsto_inv_atTop_zero.comp many
  have lb := (ilim.mul (tlim.pow 2)).sub (zlim.mul tlim)
  simp only [one_pow,mul_one,sub_zero] at lb
  filter_upwards [lb.eventually_const_lt below,eventually_gt_atTop (0:ℕ),(tendsto_atTop.mp many) 1] with n lt np large
  have vpos : 0<(n.primeCounting:ℝ) := lt_of_not_ge fun h => by
    have z : (n.primeCounting:ℝ)=0 := le_antisymm h (by positivity)
    norm_num [z] at large
  have hpos : 0<(H n:ℝ) := lt_of_not_ge fun h => by
    have z : (H n:ℝ)=0 := le_antisymm h (by positivity)
    norm_num [z] at large
  have bd : (((H n:ℝ)*(bothSeeds n).card)^2:ℝ) ≤ ((n:ℝ)+H n)*((H n:ℝ)*(bothSeeds n).card+2*exactPairWeight n (H n)) := by
    exact_mod_cast exact_pair_finite n (H n)
  exact lt.trans_le (normalized_lower (by exact_mod_cast np) hpos vpos bd)

#print axioms mesoscopic_exact_pairs

private lemma chebyshev_lower : ∀ᶠ n : ℕ in atTop,
    (n:ℝ)/4 ≤ (n.primeCounting:ℝ)*Real.log n := by
  have inc : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n:ℝ)≤(n:ℝ)+1) tendsto_natCast_atTop_atTop
  have low := inc.eventually (Real.isLittleO_log_id_atTop.bound (by norm_num : 0<(1:ℝ)/8))
  filter_upwards [low,eventually_ge_atTop (2:ℕ)] with n sm hn
  have nr : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have sm' : Real.log ((n:ℝ)+1) ≤ 1/8*((n:ℝ)+1) := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith : 1≤(n:ℝ)+1)),
      abs_of_nonneg (by linarith : 0≤(n:ℝ)+1)] using sm
  have h := (div_le_iff₀ (Real.log_pos nr)).mp (Chebyshev.pi_ge n)
  have hc : (1:ℝ)/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith only [nr,sm',h,mul_le_mul_of_nonneg_left hc (by linarith : 0≤(n:ℝ))]

/-- In particular, cutoffs growing faster than log N and slower than N
suffice without an assumption on the prime counting function. -/
theorem logarithmic_to_sublinear (H : ℕ → ℕ)
    (short : Tendsto (fun n : ℕ => (H n:ℝ)/n) atTop (𝓝 0))
    (long : Tendsto (fun n : ℕ => (H n:ℝ)/Real.log n) atTop atTop)
    {c : ℝ} (below : c<1) :
    ∀ᶠ n : ℕ in atTop, c < 2*(n:ℝ)*exactPairWeight n (H n)/((H n:ℝ)^2*(n.primeCounting:ℝ)^2) := by
  apply mesoscopic_exact_pairs H short _ below
  have unbounded := long.atTop_mul_const (by norm_num : 0<(1:ℝ)/4)
  apply tendsto_atTop_mono' _ _ unbounded
  filter_upwards [chebyshev_lower,eventually_ge_atTop (2:ℕ)] with n little hn
  have nr : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have lg := Real.log_pos nr
  have nn : 0<(n:ℝ) := by linarith
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_left little (Nat.cast_nonneg (α:=ℝ) (H n))]

#print axioms logarithmic_to_sublinear

end CunninghamChain.GapWindow
