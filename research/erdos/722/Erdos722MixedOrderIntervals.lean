import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Relative gaps between the mixed punctured orders

The logarithms of powers of four and twenty-five can be arbitrarily close
without being equal. A finite string of mixed products then covers one
factor of four up to any prescribed relative error. Multiplication by
four repeats this covering at every larger scale.
-/

namespace Erdos722.PointedProduct.Mixed
open Filter Topology

private def generated (z : ℝ) := ∃ a b : ℕ, z=a*Real.log 4+b*Real.log 25

private theorem sum_mem {x y : ℝ} (hx : generated x) (hy : generated y) : generated (x+y) := by
  obtain ⟨a,b,rfl⟩ := hx
  obtain ⟨c,d,rfl⟩ := hy
  exact ⟨a+c,b+d,by push_cast; ring⟩

private theorem nat_mul_mem {x : ℝ} (n : ℕ) (hx : generated x) : generated (n*x) := by
  obtain ⟨a,b,rfl⟩ := hx
  exact ⟨n*a,n*b,by push_cast; ring⟩

private theorem four_mem : generated (Real.log 4) := ⟨1,0,by norm_num⟩
private theorem five_mem : generated (Real.log 25) := ⟨0,1,by norm_num⟩

private theorem unequal (j k : ℕ) (hk : 0<k) :
    (j:ℝ)*Real.log 4≠k*Real.log 25 := by
  intro h
  rw [← Real.log_pow,← Real.log_pow] at h
  have eq := (Real.log_injOn_pos (show (0:ℝ)<4^j by positivity) (show (0:ℝ)<25^k by positivity) h)
  have hnat : (4:ℕ)^j=25^k := by exact_mod_cast eq
  have hdiv : 5 ∣ (4:ℕ)^j := hnat ▸ (by decide : 5∣25).trans (dvd_pow_self _ hk.ne')
  exact (by decide : ¬5∣4) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hdiv)

private theorem near {η : ℝ} (hη : 0<η) :
    ∃ u v, generated u ∧ generated v ∧ u<v ∧ v-u<η := by
  let a := Real.log 4
  let b := Real.log 25
  have ha : 0<a := Real.log_pos (by norm_num)
  have hab : a<b := Real.log_lt_log (by norm_num) (by norm_num)
  obtain ⟨n,hn⟩ := exists_nat_gt (a/η+1)
  have hn' : 0<n := by exact_mod_cast (show (0:ℝ)<n by linarith [div_pos ha hη])
  obtain ⟨j,k,hk,_,hd⟩ := Real.exists_int_int_abs_mul_sub_le (b/a) hn'
  have hk' : (1:ℝ)≤k := by exact_mod_cast (show (1:ℤ)≤k by omega)
  have h1 : (1:ℝ)/(n+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hj : (0:ℤ)≤j := by
    have h := (abs_le.mp (hd.trans h1)).2
    have hm := mul_le_mul_of_nonneg_right hk' (div_pos (ha.trans hab) ha).le
    have hb : 1<b/a := (one_lt_div ha).mpr hab
    exact_mod_cast (show (0:ℝ)≤j by linarith)
  let u := (j.toNat:ℝ)*a
  let v := (k.toNat:ℝ)*b
  have hu : generated u := nat_mul_mem _ four_mem
  have hv : generated v := nat_mul_mem _ five_mem
  have hne : u≠v := unequal _ _ (by omega)
  have hsmall : |v-u|<η := by
    have e : v-u=((k:ℝ)*(b/a)-j)*a := by
      dsimp [v,u]
      have cast_eq {w : ℤ} (hw : 0≤w) : (w.toNat:ℝ)=(w:ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hw
      rw [cast_eq hj,cast_eq hk.le]
      field_simp
    rw [e,abs_mul,abs_of_pos ha]
    refine (mul_le_mul_of_nonneg_right hd ha.le).trans_lt ?_
    have h := (div_lt_iff₀ hη).mp (show a/η<(n:ℝ)+1 by linarith)
    rw [one_div_mul_eq_div]
    exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨u,v,hu,hv,h,(abs_lt.mp hsmall).2⟩
  · exact ⟨v,u,hv,hu,h,by linarith [(abs_lt.mp hsmall).1]⟩

/-- Every sufficiently large logarithmic interval of the given positive length
contains a nonnegative integral combination of the two logarithms. -/
private theorem eventual_logs {η : ℝ} (he : 0<η) :
    ∀ᶠ x : ℝ in atTop, ∃ y, generated y ∧ x≤y ∧ y<x+η := by
  obtain ⟨u,v,hu,hv,huv,hd⟩ := near he
  let a := Real.log 4
  let d := v-u
  have ha : 0<a := Real.log_pos (by norm_num)
  have hpos : 0<d := sub_pos.mpr huv
  let M := ⌈a/d⌉₊
  have hM : a≤(M:ℝ)*d := (div_le_iff₀ hpos).mp (Nat.le_ceil _)
  filter_upwards [eventually_ge_atTop (M*u)] with x hx
  let j := ⌊(x-M*u)/a⌋₊
  let r := x-M*u-j*a
  have hr : 0≤r := by
    have h := (le_div_iff₀ ha).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hx) ha.le))
    dsimp [r,j]; linarith
  have hra : r<a := by
    have h := (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one ((x-M*u)/a))
    dsimp [r,j]; linarith
  let i := ⌈r/d⌉₊
  have hi : i≤M := Nat.ceil_le.mpr ((div_le_iff₀ hpos).mpr (hra.le.trans hM))
  have low : r≤(i:ℝ)*d := (div_le_iff₀ hpos).mp (Nat.le_ceil _)
  have high : (i:ℝ)*d<r+d := by
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hr hpos.le)) hpos
    rw [add_mul,div_mul_cancel₀ _ hpos.ne',one_mul] at h
    exact h
  let y := (j:ℝ)*a+(M-i:ℕ)*u+i*v
  have hy : generated y := sum_mem (sum_mem (nat_mul_mem _ four_mem) (nat_mul_mem _ hu)) (nat_mul_mem _ hv)
  have eq : y=x-r+i*d := by dsimp [y,r,d]; rw [Nat.cast_sub hi]; ring
  exact ⟨y,hy,by rw [eq]; linarith,by rw [eq]; linarith⟩

/-- Every sufficiently large real interval [x,(1+ε)x) contains 4ᵃ25ᵇ. -/
theorem dense_mixed_orders {ε : ℝ} (he : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ∃ a b : ℕ, x≤(4:ℝ)^a*25^b ∧ (4:ℝ)^a*25^b<(1+ε)*x := by
  have h := Real.tendsto_log_atTop.eventually (eventual_logs (Real.log_pos (show 1<1+ε by linarith)))
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with x hx hpos
  obtain ⟨y,⟨a,b,rfl⟩,hlo,hhi⟩ := hx
  have eq : Real.log ((4:ℝ)^a*25^b)=a*Real.log 4+b*Real.log 25 := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  refine ⟨a,b,(Real.log_le_log_iff hpos (by positivity)).mp (eq.symm ▸ hlo),?_⟩
  apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
  rw [eq,Real.log_mul (by positivity) hpos.ne',add_comm (Real.log (1+ε))]
  exact hhi

#print axioms dense_mixed_orders
end Erdos722.PointedProduct.Mixed
