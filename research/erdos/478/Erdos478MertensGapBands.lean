import Erdos478GapCutoff

/-!
# Mertens products on a power-sized band of prime lengths

For fixed positive integers a<b and C, the finite Euler product over the
primes in (Ct^a,t^b] tends to a/b. The constant in Mertens' product cancels.
-/

namespace Erdos478.GapBands
open Finset Filter Topology GapSieve GapVariance
noncomputable section

def band (lo hi : ℕ) : Finset Nat.Primes := through hi \ through lo

def euler (s : Finset Nat.Primes) : ℝ := ∏ i ∈ s, (1-weight i)

/-- Mertens' product asymptotic, in the normalization used by the gap sieve. -/
def MertensProduct : Prop := ∃ A : ℝ, 0<A ∧
  Tendsto (fun n : ℕ => euler (through n)*Real.log n) atTop (𝓝 A)

theorem euler_pos (s : Finset Nat.Primes) : 0<euler s := by
  apply prod_pos
  intro i _
  have hi : (1:ℝ) < (i.val:ℝ) := by exact_mod_cast i.property.one_lt
  exact sub_pos.mpr (show 1/(i.val:ℝ)<1 from (div_lt_one (zero_lt_one.trans hi)).mpr hi)

theorem band_product {lo hi : ℕ} (h : lo≤hi) :
    euler (band lo hi)=euler (through hi)/euler (through lo) := by
  apply (eq_div_iff (euler_pos _).ne').mpr
  apply prod_sdiff
  intro i hmem
  exact mem_through.mpr ((mem_through.mp hmem).trans h)

private theorem tendsto_scale {C a : ℕ} (hC : 0<C) (ha : 0<a) :
    Tendsto (fun t : ℕ => C*t^a) atTop atTop := by
  apply tendsto_atTop_mono (f:=fun t : ℕ => t^a)
  · intro t
    simpa using Nat.mul_le_mul_right (t^a) (show 1≤C by omega)
  · exact tendsto_pow_atTop ha.ne'

private theorem log_scale {C a : ℕ} (hC : 0<C) :
    Tendsto (fun t : ℕ => Real.log (C*t^a : ℕ)/Real.log t) atTop (𝓝 (a:ℝ)) := by
  have l := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc := (tendsto_const_nhds (x:=Real.log (C:ℝ))).div_atTop l
  have hh := hc.add (tendsto_const_nhds (x:=(a:ℝ)))
  rw [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with t ht
  have ht' : 1<(t:ℝ) := by exact_mod_cast (show 1<t by omega)
  have hC' : (C:ℝ)≠0 := by exact_mod_cast hC.ne'
  simp only [Nat.cast_mul,Nat.cast_pow,Real.log_mul hC' (pow_ne_zero _ (zero_lt_one.trans ht').ne'),
    Real.log_pow]
  simp only [Function.comp_apply]
  field_simp [(Real.log_pos ht').ne']

private theorem product_scale {A : ℝ}
    (hm : Tendsto (fun n : ℕ => euler (through n)*Real.log n) atTop (𝓝 A))
    {C a : ℕ} (hC : 0<C) (ha : 0<a) :
    Tendsto (fun t : ℕ => euler (through (C*t^a))*Real.log t) atTop (𝓝 (A/a)) := by
  have h := (hm.comp (tendsto_scale hC ha)).div (log_scale (a:=a) hC) (by exact_mod_cast ha.ne')
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with t ht
  have ht' : 1<(t:ℝ) := by exact_mod_cast (show 1<t by omega)
  have hs : 1<C*t^a := by
    have h₁ : 1<t^a := Nat.one_lt_pow ha.ne' (by omega)
    have h₂ := Nat.mul_le_mul_right (t^a) (show 1≤C by omega)
    omega
  have hs' : 1<(C*t^a : ℕ) := hs
  have hl := Real.log_pos (by exact_mod_cast hs' : (1:ℝ)<(C*t^a : ℕ))
  change (euler (through (C*t^a))*Real.log (C*t^a : ℕ))/(Real.log (C*t^a : ℕ)/Real.log t)=_
  field_simp [hl.ne',(Real.log_pos ht').ne']

/-- The finite prime product on an interval whose endpoints have
logarithmic orders a and b tends to their ratio. -/
theorem band_limit (hM : MertensProduct) {C a b : ℕ} (hC : 0<C) (ha : 0<a) (hab : a<b) :
    Tendsto (fun t : ℕ => euler (band (C*t^a) (t^b))) atTop (𝓝 ((a:ℝ)/b)) := by
  obtain ⟨A,hA,hm⟩ := hM
  have hb : 0<b := by omega
  have up := product_scale hm (by decide : 0<1) hb
  simp only [one_mul] at up
  have h := up.div (product_scale hm hC ha) (div_ne_zero hA.ne' (by exact_mod_cast ha.ne'))
  rw [show A/(b:ℝ)/(A/(a:ℝ))=a/b by field_simp] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (max C 2)] with t ht
  have hav : C*t^a≤t^b := by
    calc C*t^a ≤ t*t^a := Nat.mul_le_mul_right _ (by omega)
         _ = t^(a+1) := (pow_succ' ..).symm
         _ ≤ t^b := Nat.pow_le_pow_right (by omega) (by omega)
  rw [band_product hav]
  exact mul_div_mul_right _ _ (Real.log_pos (by exact_mod_cast (show 1<t by omega))).ne'

#print axioms euler_pos
#print axioms band_product
#print axioms band_limit
end
end Erdos478.GapBands
