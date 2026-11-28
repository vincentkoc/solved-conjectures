import CunninghamGapTail
import CunninghamSingularSeriesGrowth
import Mathlib.NumberTheory.Primorial

/-! Average of the full paired singular series over the gap between opposite-kind seeds. -/

namespace CunninghamChain.GapMean

open Finset Real Filter BatemanHornConjecture
open scoped Topology

private noncomputable abbrev B (k Y : ℕ) := BatemanHornPartialProduct (chainForms 1 k) Y
private abbrev cutoff (N : ℕ) := Nat.log 16 N

noncomputable def average (f : ℕ → ℝ) (N : ℕ) := (∑ n∈range N, f n)/(N:ℝ)

/-- The convergent singular series for gap h+2, with zero allowed for obstructed gaps. -/
noncomputable def series (k l h : ℕ) := limitingWeight k l h * chainConstant (k+l)

theorem series_limit {k l : ℕ} (pos : 0<k+l) (h : ℕ) :
    Tendsto (fun Y => pairProduct k l Y (h+2)) atTop (𝓝 (series k l h)) := by
  apply (tendsto_const_nhds (x:=limitingWeight k l h) |>.mul (chainConstant_spec pos).2.1).congr'
  filter_upwards [eventually_ge_atTop (stop k l h)] with Y past
  rw [pairProduct_eq_weight,stabilized_weight _ _ _ _ past]

private theorem cutoff_grows : Tendsto cutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (16^b)] with N hn
  exact (Nat.le_log_iff_pow_le (by decide : 1<16) ((pow_pos (by decide : 0<(16:ℕ)) b).trans_le hn).ne').mpr hn

private lemma modulus_bound (Y : ℕ) : (∏ q∈Y.primesBelow, q)≤4^Y := by
  apply le_trans _ (primorial_le_four_pow Y)
  rw [primorial_eq_prod_primesLE]
  apply Nat.le_of_dvd (prod_pos fun q h => (Nat.prime_of_mem_primesLE h).pos)
  apply prod_dvd_prod_of_subset
  intro q h
  exact Nat.mem_primesLE.mpr ⟨(Nat.lt_of_mem_primesBelow h).le,Nat.prime_of_mem_primesBelow h⟩

private lemma incomplete_small {N : ℕ} (np : 0<N) :
    ((∏ q∈(cutoff N).primesBelow, q : ℕ):ℝ)/N ≤ (1/4:ℝ)^(cutoff N) := by
  let Y := cutoff N
  have lower : (16:ℝ)^Y≤N := by exact_mod_cast Nat.pow_log_le_self 16 np.ne'
  have upper : ((∏ q∈Y.primesBelow, q : ℕ):ℝ)≤(4:ℝ)^Y := by exact_mod_cast modulus_bound Y
  calc
    _ ≤ (4:ℝ)^Y/16^Y := div_le_div₀ (by positivity) upper (by positivity) lower
    _ = _ := by rw [←div_pow]; norm_num [Y]

private lemma moving_truncation {k l : ℕ} (hk : 0<k) (hl : 0<l) :
    Tendsto (fun N => average (fun h => pairProduct k l (cutoff N) (h+2)) N) atTop
      (𝓝 (chainConstant k*chainConstant l)) := by
  let b (N : ℕ) := B k (cutoff N)*B l (cutoff N)
  let e (N : ℕ) := (1/4:ℝ)^(cutoff N)*b N
  have bLim := ((chainConstant_spec hk).2.1.comp cutoff_grows).mul ((chainConstant_spec hl).2.1.comp cutoff_grows)
  change Tendsto b atTop _ at bLim
  have shr := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/4:ℝ)) (by norm_num)).comp cutoff_grows
  have eLim : Tendsto e atTop (𝓝 0) := by simpa [e] using shr.mul bLim
  have bounds : ∀ᶠ N in atTop, |average (fun h => pairProduct k l (cutoff N) (h+2)) N - b N| ≤ e N := by
    filter_upwards [eventually_ge_atTop 1] with N np
    have pos : (0:ℝ)<N := by exact_mod_cast np
    have err := truncated_gap_mean k l (cutoff N) N 2
    have Bpos (m) : 0≤B m (cutoff N) := by
      unfold B; rw [←product_single]; exact prod_nonneg fun q h => (single_pos m q (Nat.prime_of_mem_primesBelow h)).le
    have bn : 0≤b N := mul_nonneg (Bpos k) (Bpos l)
    have step := div_le_div_of_nonneg_right err pos.le
    change |(∑ h∈range N, pairProduct k l (cutoff N) (h+2)) - (N:ℝ)*b N|/N ≤ ((∏ q∈(cutoff N).primesBelow, q : ℕ):ℝ)*b N/N at step
    unfold average
    calc
      _ = |((∑ h∈range N, pairProduct k l (cutoff N) (h+2))-(N:ℝ)*b N)/N| := by
        rw [sub_div,mul_div_cancel_left₀ _ pos.ne']
      _ ≤ ((∏ q∈(cutoff N).primesBelow, q : ℕ):ℝ)*b N/N := by simpa only [abs_div,abs_of_pos pos] using step
      _ = ((∏ q∈(cutoff N).primesBelow, q : ℕ):ℝ)/(N:ℝ)*b N := by ring
      _ ≤ e N := mul_le_mul_of_nonneg_right (incomplete_small np) bn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun N => b N-e N) (h:=fun N => b N+e N)
  · simpa using bLim.sub eLim
  · simpa using bLim.add eLim
  · filter_upwards [bounds] with N h; linarith [(abs_le.mp h).1]
  · filter_upwards [bounds] with N h; linarith [(abs_le.mp h).2]

private noncomputable def tailConstant (k l : ℕ) : ℝ :=
  2*((k+l:ℕ):ℝ)*(k*l:ℕ)*(((k+l:ℕ):ℝ)*log 2+2*log 16)

private lemma moving_tail {k l N h : ℕ} (lt : h<N) (large : threshold (k+l)≤cutoff N) :
    weight k l (cutoff N) h ≤ limitingWeight k l h ∧ limitingWeight k l h ≤
      weight k l (cutoff N) h * exp (tailConstant k l/log (cutoff N)) := by
  let m := k+l
  let Y := cutoff N
  have yp : 1<Y := by change threshold m≤Y at large; unfold threshold at large; have := Nat.zero_le (2^(m+2)); omega
  have yr : (1:ℝ)<Y := by exact_mod_cast yp
  have p2 : 0<log 2 := log_pos (by norm_num)
  have p16 : 0<log 16 := log_pos (by norm_num)
  have yh : ((h+2:ℕ):ℝ)≤(16:ℝ)^(Y+1) := by
    exact_mod_cast (show h+2≤16^(Y+1) by have H : N<16^(Y+1) := Nat.lt_pow_succ_log_self (by decide : 1<16) N; omega)
  have logh := log_le_log (by positivity : (0:ℝ)<(h+2:ℕ)) yh
  rw [log_pow] at logh
  push_cast at logh
  have dl := log_le_log (by exact_mod_cast exceptional_pos k l h) (Nat.cast_le.mpr (exceptional_le k l h) : ((exceptionalProduct k l h:ℕ):ℝ)≤_)
  push_cast at dl
  rw [log_pow,log_mul (by positivity) (by positivity),log_pow] at dl
  have cap : log (exceptionalProduct k l h) ≤ ((k*l:ℕ):ℝ) * (Y* ((m:ℝ)*log 2+2*log 16)) := by
    apply dl.trans
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change ((k:ℝ)+l)*log 2+log (h+2)≤_
    have mr : (m:ℝ)=(k:ℝ)+l := Nat.cast_add ..
    rw [←mr]
    nlinarith [mul_nonneg (sub_nonneg.mpr yr.le) (mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) p2.le),
      mul_nonneg (sub_nonneg.mpr yr.le) p16.le,logh]
  obtain ⟨low,high⟩ := weight_tail k l h Y large
  refine ⟨low,high.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (weight_nonneg ..))⟩
  rw [div_le_div_iff₀ (mul_pos (by linarith) (log_pos yr)) (log_pos yr)]
  have bound := mul_le_mul_of_nonneg_left cap (show 0≤2*(m:ℝ) by positivity)
  unfold tailConstant
  calc
    _ ≤ (2*(m:ℝ)*(((k*l:ℕ):ℝ)*(Y*((m:ℝ)*log 2+2*log 16)))) * log Y :=
      mul_le_mul_of_nonneg_right bound (log_pos yr).le
    _ = _ := by dsimp [m,Y]; ring

private lemma average_mul (f : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    average (fun h => f h*c) N = average f N*c := by
  simp only [average,←sum_mul]
  ring

private lemma average_mono {f g : ℕ → ℝ} (N : ℕ) (le : ∀ h<N, f h≤g h) :
    average f N≤average g N := div_le_div_of_nonneg_right
      (sum_le_sum (fun h mem => le h (mem_range.mp mem))) (by positivity)

/-- The mean of the paired singular series is the product of the two single-chain
constants. The first seed varies independently of the nonnegative gap offset. -/
theorem mean_series {k l : ℕ} (hk : 0<k) (hl : 0<l) :
    Tendsto (average (series k l)) atTop (𝓝 (chainConstant k*chainConstant l)) := by
  let m := k+l
  have mp : 0 < m := by dsimp [m]; omega
  let a N := average (fun h => pairProduct k l (cutoff N) (h+2)) N
  let b N := B m (cutoff N)
  let t N := exp (tailConstant k l/log (cutoff N))
  have cp := (chainConstant_spec mp).1
  have ratioLim := (moving_truncation hk hl).div ((chainConstant_spec mp).2.1.comp cutoff_grows) cp.ne'
  change Tendsto (fun N => a N/b N) atTop _ at ratioLim
  have lg : Tendsto (fun N : ℕ => log (cutoff N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp cutoff_grows)
  have dec := (tendsto_const_nhds (x:=tailConstant k l)).div_atTop lg
  have tl : Tendsto t atTop (𝓝 1) := by simpa only [t,Function.comp_def,Real.exp_zero] using (Real.continuous_exp.tendsto (0:ℝ)).comp dec
  have bounds (N : ℕ) (large : threshold m≤cutoff N) : a N/b N ≤ average (limitingWeight k l) N ∧
      average (limitingWeight k l) N ≤ a N/b N*t N := by
    let f := weight k l (cutoff N)
    have bp : 0<b N := by
      dsimp [b,B]; rw [←product_single]; exact prod_pos fun q h => single_pos _ _ (Nat.prime_of_mem_primesBelow h)
    have eq : a N/b N = average f N := by
      have af : a N=average (fun h => f h*b N) N := by
        dsimp [a,f,b,B,m]
        simp only [pairProduct_eq_weight]
      rw [af,average_mul,mul_div_cancel_right₀ _ bp.ne']
    rw [eq,←average_mul]
    exact ⟨average_mono N (fun h hh => (moving_tail hh large).1),
      average_mono N (fun h hh => (moving_tail hh large).2)⟩
  have one := (tendsto_atTop.mp cutoff_grows) (threshold m)
  have gl : Tendsto (average (limitingWeight k l)) atTop (𝓝 (chainConstant k*chainConstant l/chainConstant m)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ratioLim
      (by simpa only [mul_one] using ratioLim.mul tl)
    · filter_upwards [one] with N h using (bounds N h).1
    · filter_upwards [one] with N h using (bounds N h).2
  have ans := gl.mul_const (chainConstant m)
  rw [div_mul_cancel₀ _ cp.ne'] at ans
  apply ans.congr
  intro N
  exact (average_mul _ _ _).symm

#print axioms mean_series

#print axioms series_limit

end CunninghamChain.GapMean
