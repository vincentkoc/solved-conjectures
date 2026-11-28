import Erdos478PowerBandQuantiles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A localized factorial deficit for every real exponent

The lower endpoint of the allowed gap interval is the ceiling of K^α.
This gives the prime proportion estimate at every sufficiently large
integral upper cutoff K, with no restriction to perfect powers.
-/

namespace Erdos478.GapBands
open Finset Filter Topology GapSieve GapDensity
noncomputable section

def demand (α : ℝ) (K : ℕ) := ⌈(K:ℝ)^α⌉₊

private theorem demand_bounds {α : ℝ} (hα : 0≤α) {K : ℕ} (hK : 1≤K) :
    (K:ℝ)^α≤(demand α K:ℝ) ∧ (demand α K:ℝ)≤2*(K:ℝ)^α := by
  have h := Real.one_le_rpow (by exact_mod_cast hK : (1:ℝ)≤K) hα
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := Nat.ceil_lt_add_one (show 0≤(K:ℝ)^α by positivity)
  dsimp [demand]
  linarith

private theorem scale_diverges {C : ℕ} {α : ℝ} (hC : 0<C) (ha : 0<α) :
    Tendsto (fun K => C*demand α K) atTop atTop := by
  have h : Tendsto (demand α) atTop atTop :=
    tendsto_nat_ceil_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono (fun K => by simpa using Nat.mul_le_mul_right (demand α K) hC) h

private theorem log_demand {C : ℕ} {α : ℝ} (hC : 0<C) (ha : 0<α) :
    Tendsto (fun K : ℕ => Real.log (C*demand α K : ℕ)/Real.log K) atTop (𝓝 α) := by
  have cl : Tendsto (fun K : ℕ => Real.log (2*(C:ℝ))/Real.log K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have tlim := cl.add (tendsto_const_nhds (x:=α))
  rw [zero_add] at tlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x:=α)) tlim
  · filter_upwards [eventually_ge_atTop 2] with K hK
    have hr : 1<(K:ℝ) := by exact_mod_cast (show 1<K by omega)
    have h := (demand_bounds ha.le (by omega : 1≤K)).1
    have hc : (demand α K:ℝ)≤(C*demand α K : ℕ) := by
      exact_mod_cast (show demand α K≤C*demand α K by simpa using Nat.mul_le_mul_right _ hC)
    apply (le_div_iff₀ (Real.log_pos hr)).mpr
    rw [← Real.log_rpow (zero_lt_one.trans hr)]
    exact Real.log_le_log (by positivity) (h.trans hc)
  · filter_upwards [eventually_ge_atTop 2] with K hK
    have hr : 1<(K:ℝ) := by exact_mod_cast (show 1<K by omega)
    have h := (demand_bounds ha.le (by omega : 1≤K)).2
    have hc : (0:ℝ)<C := by exact_mod_cast hC
    have hb : ((C*demand α K:ℕ):ℝ)≤2*(C:ℝ)*(K:ℝ)^α := by
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left h hc.le]
    have pos : (0:ℝ)<(C*demand α K : ℕ) := by
      have hd : 0<demand α K := Nat.ceil_pos.mpr (by positivity)
      exact_mod_cast Nat.mul_pos hC hd
    have hl := Real.log_le_log pos hb
    rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (zero_lt_one.trans hr)] at hl
    apply (div_le_iff₀ (Real.log_pos hr)).mpr
    rw [add_mul,div_mul_cancel₀ _ (Real.log_pos hr).ne']
    exact hl

private theorem inner_le {C : ℕ} {α : ℝ} (ha : 0<α) (h1 : α<1) :
    ∀ᶠ K : ℕ in atTop, C*demand α K≤K := by
  have h := ((tendsto_rpow_atTop (show 0<1-α by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (2*(C:ℝ))
  filter_upwards [h,eventually_ge_atTop 1] with K hK hpos
  have hr : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hD := (demand_bounds ha.le hpos).2
  change 2*(C:ℝ)≤(K:ℝ)^(1-α) at hK
  have hrpow : (K:ℝ)^(1-α)*(K:ℝ)^α=K := by rw [← Real.rpow_add hr]; simp
  have hle := mul_le_mul_of_nonneg_right hK (show 0≤(K:ℝ)^α by positivity)
  rw [hrpow] at hle
  have res : (C:ℝ)*(demand α K:ℝ)≤K := by
    nlinarith only [mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg C : (0:ℝ)≤C),hle]
  exact_mod_cast res

theorem real_band_limit (hM : MertensProduct) {C : ℕ} {α : ℝ} (hC : 0<C) (ha : 0<α)
    (h1 : α<1) : Tendsto (fun K => euler (band (C*demand α K) K)) atTop (𝓝 α) := by
  obtain ⟨A,hA,hm⟩ := hM
  have h := (hm.div (hm.comp (scale_diverges hC ha)) hA.ne').mul (log_demand hC ha)
  rw [div_self hA.ne',one_mul] at h
  apply h.congr'
  filter_upwards [inner_le (C:=C) ha h1,eventually_ge_atTop 2,(scale_diverges hC ha).eventually_ge_atTop 2]
    with K hlo hK hD
  rw [band_product hlo]
  change ((euler (through K)*Real.log K)/(euler (through (C*demand α K))*Real.log (C*demand α K : ℕ)))*
    (Real.log (C*demand α K : ℕ)/Real.log K)=_
  have lK := Real.log_pos (by exact_mod_cast (show 1<K by omega) : (1:ℝ)<K)
  have lD := Real.log_pos (by exact_mod_cast (show 1<C*demand α K by omega) : (1:ℝ)<(C*demand α K : ℕ))
  field_simp [lD.ne',lK.ne',(euler_pos _).ne']

theorem real_band_of_inputs (pit : DegreeOnePrimeIdealTheorem) (hm : MertensProduct)
    {α ε : ℝ} (ha : 0<α) (h1 : α<1) (hε : 0<ε) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      1-α-ε < fraction X (witnessed (demand α K) K (demand α K)) := by
  apply frequency_of_band_limits pit (demand α) id _ _ hε
  · filter_upwards [eventually_ge_atTop 1] with K hK
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast (show 0<K by omega)) _)
  · exact fun _ hC => real_band_limit hm hC ha h1

#print axioms real_band_limit
#print axioms real_band_of_inputs
end
end Erdos478.GapBands
