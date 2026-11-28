import Erdos478PrimeBandWeights

/-!
# Selected prime lengths in every proportional interval

A natural asymptotic for a selected von Mangoldt sum gives the prime
count in (K,H(K)] whenever H(K)/K tends to a constant greater than one.
The factor log H(K)/log K tends to one throughout this regime.
-/

namespace Erdos478.BandWeights
open Finset Filter
open scoped Topology Classical
noncomputable section

def lengths (P : ℕ → Prop) (K H : ℕ) := (Ioc K H).filter fun n => P n ∧ n.Prime

private theorem log_bounds (P : ℕ → Prop) {K H : ℕ} (hK : 0<K) (hH : K≤H) :
    (lengths P K H).card*Real.log K≤primeWeight P H-primeWeight P K ∧
    primeWeight P H-primeWeight P K≤(lengths P K H).card*Real.log H := by
  have eq : primeWeight P H-primeWeight P K=∑ n∈lengths P K H, Real.log n := by
    unfold primeWeight
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le K) hH,sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    simp [lengths,sum_filter]
  rw [eq]
  constructor
  · simpa only [sum_const,nsmul_eq_mul] using sum_le_sum
      (s:=lengths P K H) (f:=fun _ => Real.log K) (g:=fun n : ℕ => Real.log n)
      (fun n hn => Real.log_le_log (by exact_mod_cast hK)
        (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).1.le))
  · simpa only [sum_const,nsmul_eq_mul] using sum_le_sum
      (s:=lengths P K H) (f:=fun n : ℕ => Real.log n) (g:=fun _ => Real.log H)
      (fun n hn => Real.log_le_log (by exact_mod_cast hK.trans (mem_Ioc.mp (mem_filter.mp hn).1).1)
        (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).2))

theorem eventually_le_upper {H : ℕ → ℕ} {L : ℝ} (hL : 1<L)
    (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L)) : ∀ᶠ K in atTop, K≤H K := by
  filter_upwards [h.eventually_const_lt hL,eventually_gt_atTop 0] with K hk hk'
  have hpos : 0<(K:ℝ) := by exact_mod_cast hk'
  have hlt := (lt_div_iff₀ hpos).mp hk
  exact_mod_cast (show (K:ℝ)≤H K by linarith)

private theorem log_ratio {H : ℕ → ℕ} {L : ℝ} (hL : 1<L)
    (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => Real.log (H K)/Real.log K) atTop (𝓝 1) := by
  have hlog := (Real.continuousAt_log (by linarith : L≠0)).tendsto.comp h
  have small := hlog.div_atTop (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have lim := (tendsto_const_nhds (x:=(1:ℝ))).add small
  rw [add_zero] at lim
  apply lim.congr'
  filter_upwards [eventually_le_upper hL h,eventually_gt_atTop 1] with K hu hk
  have a : 1<(K:ℝ) := by exact_mod_cast hk
  have b : 0<(H K:ℝ) := by exact_mod_cast (show 0<H K by omega)
  change 1+Real.log ((H K:ℝ)/K)/Real.log K=_
  rw [Real.log_div b.ne' (by linarith)]
  field_simp [(Real.log_pos a).ne']
  ring

theorem length_asymptotic {P : ℕ → Prop} {c L : ℝ} (input : countingInput P c) {H : ℕ → ℕ}
    (hL : 1<L) (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => ((lengths P K (H K)).card:ℝ)*Real.log K/K) atTop (𝓝 (c*(L-1))) := by
  have ge := eventually_le_upper hL h
  have htop : Tendsto H atTop atTop := tendsto_atTop_mono' atTop ge tendsto_id
  have hw := prime_weight_limit input
  have diff : Tendsto (fun K : ℕ => (primeWeight P (H K)-primeWeight P K)/K) atTop (𝓝 (c*(L-1))) := by
    rw [mul_sub,mul_one]
    apply (((hw.comp htop).mul h).sub hw).congr'
    filter_upwards [ge,eventually_gt_atTop 0] with K hu hk
    have pos : 0<(H K:ℝ) := by exact_mod_cast (show 0<H K by omega)
    change primeWeight P (H K)/(H K)*(H K/K)-primeWeight P K/K=_
    field_simp [pos.ne']
  have low := diff.div (log_ratio hL h) one_ne_zero
  rw [div_one] at low
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low diff
  · filter_upwards [ge,eventually_gt_atTop 1] with K hu hk
    obtain ⟨_,ub⟩ := log_bounds P (by omega : 0<K) hu
    have kpos : 0<(K:ℝ) := by positivity
    have lk := Real.log_pos (show (1:ℝ)<K by exact_mod_cast hk)
    have lh := Real.log_pos (show (1:ℝ)<H K by exact_mod_cast hk.trans_le hu)
    change (primeWeight P (H K)-primeWeight P K)/K/(Real.log (H K)/Real.log K)≤_
    apply (div_le_iff₀ (div_pos lh lk)).mpr
    calc
      _ ≤ ((lengths P K (H K)).card:ℝ)*Real.log (H K)/K := div_le_div_of_nonneg_right ub kpos.le
      _ = _ := by field_simp
  · filter_upwards [ge,eventually_gt_atTop 0] with K hu hk
    exact div_le_div_of_nonneg_right (log_bounds P hk hu).1 (Nat.cast_nonneg _)

#print axioms eventually_le_upper
#print axioms length_asymptotic
end
end Erdos478.BandWeights
