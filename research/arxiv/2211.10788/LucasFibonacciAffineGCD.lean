import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciSmoothBlocks

/-! Common divisors of affine-index upper Lucas–Fibonacci sums. -/

namespace Arxiv.«2211.10788»
open QuadraticAlgebra
private abbrev FibAlg (R : Type*) [CommRing R] := QuadraticAlgebra R 1 1

private theorem fib_root_sq {R : Type*} [CommRing R] :
    (ω : FibAlg R)^2 = ω + 1 := by
  rw [pow_two,omega_mul_omega_eq_add]
  simp [add_comm]

private theorem fib_root_unit {R : Type*} [CommRing R] : IsUnit (ω : FibAlg R) := by
  apply IsUnit.of_mul_eq_one (ω-1)
  linear_combination fib_root_sq (R := R)

private theorem upper_power (R : Type*) [CommRing R] (n : ℕ) :
    (ω : FibAlg R)^n = (Nat.fib n : FibAlg R)*(ω-4) + (lucasFibonacciSum n : FibAlg R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucas_fibonacci_sum_zero]
  | one => simp [lucas_fibonacci_sum_one]
  | more n h₀ h₁ =>
    rw [pow_add, fib_root_sq, mul_add, mul_one, ← pow_succ, h₁,h₀]
    rw [Nat.fib_add_two,lucas_fibonacci_sum_recurrence]
    push_cast
    ring

private def scalarEval {R : Type*} [CommRing R] (c : R) (x : FibAlg R) := x.re+c*x.im

private def rootEval {R : Type*} [CommRing R] (c : R) (hc : c^2 = c+1) : FibAlg R →+* R where
  toFun := scalarEval c
  map_zero' := by simp [scalarEval]
  map_one' := by simp [scalarEval]
  map_add' x y := by simp [scalarEval]; ring
  map_mul' x y := by simp [scalarEval]; linear_combination -(x.im*y.im)*hc

private def modFibAlg (q : ℕ) : FibAlg ℤ →+* FibAlg (ZMod q) where
  toFun x := ⟨x.re,x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private theorem modFibAlg_omega (q : ℕ) : modFibAlg q ω = ω := by ext <;> simp [modFibAlg]
/-- For slopes d < f, the imaginary coefficient of this quadratic integer
bounds the common divisors independently of the progression parameter. -/
private def obstruction (r d s f : ℕ) : FibAlg ℤ :=
  (ω-1)^(f*r) * ω^(d*s) * (ω-4)^(f-d)

private theorem obstruction_nonzero (r d s f : ℕ) (h : d < f) :
    (obstruction r d s f).im ≠ 0 := by
  intro hz
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let x := modFibAlg 11 (obstruction r d s f)
  have hxi : x.im = 0 := by change ((obstruction r d s f).im : ZMod 11) = 0; simp [hz]
  let e₁ := rootEval (4:ZMod 11) (by decide)
  let e₂ := rootEval (-3:ZMod 11) (by decide)
  have ee : e₁ x = e₂ x := by change x.re + 4*x.im = x.re+(-3)*x.im; rw [hxi]; ring
  have home (e : FibAlg (ZMod 11) →+* ZMod 11) :
      e x = (e ω-1)^(f*r)*(e ω)^(d*s)*(e ω-4)^(f-d) := by
    simp only [x,obstruction,map_mul,map_pow,map_sub,map_one,map_ofNat,modFibAlg_omega]
  have he₁ : e₁ ω = 4 := by simp [e₁,rootEval,scalarEval]
  have he₂ : e₂ ω = -3 := by simp [e₂,rootEval,scalarEval]
  rw [home,home,he₁,he₂] at ee
  simp only [sub_self,zero_pow (Nat.sub_ne_zero_of_lt h),mul_zero] at ee
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by decide : (-3:ZMod 11)-1 ≠ 0))
    (pow_ne_zero _ (by decide : (-3:ZMod 11) ≠ 0))) (pow_ne_zero _ (by decide : (-3:ZMod 11)-4 ≠ 0))) ee.symm

private theorem affine_common_dvd (q r d s f t : ℕ) (hdf : d < f)
    (ha : q ∣ lucasFibonacciSum (r+d*t)) (hb : q ∣ lucasFibonacciSum (s+f*t)) :
    q ∣ (obstruction r d s f).im.natAbs := by
  let a := r+d*t
  let b := s+f*t
  let x := (ω : FibAlg (ZMod q))
  let y := x-4
  have hpow (n : ℕ) (hh : q ∣ lucasFibonacciSum n) :
      x^n = (Nat.fib n : FibAlg (ZMod q))*y := by
    have hz := (ZMod.natCast_eq_zero_iff _ q).mpr hh
    have hz' := congrArg (algebraMap (ZMod q) (FibAlg (ZMod q))) hz
    simp only [map_natCast,map_zero] at hz'
    simpa only [hz',add_zero] using upper_power (ZMod q) n
  have hab (n : ℕ) (hh : q ∣ lucasFibonacciSum n) :
      IsUnit (Nat.fib n : ZMod q) := by
    have hh' := hpow n hh
    have hu : IsUnit (Nat.fib n : FibAlg (ZMod q)) :=
      isUnit_of_mul_isUnit_left (hh' ▸ (fib_root_unit.pow n))
    obtain ⟨z,hz⟩ := isUnit_iff_exists_inv.mp hu
    apply IsUnit.of_mul_eq_one z.re
    simpa using congrArg QuadraticAlgebra.re hz
  have hm : (Nat.fib b : FibAlg (ZMod q))^d*x^(f*a) =
      (Nat.fib a : FibAlg (ZMod q))^f * x^(d*b)*y^(f-d) := by
    rw [Nat.mul_comm f a,Nat.mul_comm d b,pow_mul,pow_mul,hpow a ha,hpow b hb,mul_pow,mul_pow]
    rw [show f = d + (f-d) by omega]
    simp only [pow_add,Nat.add_sub_cancel_left]
    ring
  have he₁ : f*a = f*r+d*f*t := by dsimp [a]; ring
  have he₂ : d*b = d*s+d*f*t := by dsimp [b]; ring
  rw [he₁,he₂,pow_add,pow_add] at hm
  have hc : (Nat.fib b : FibAlg (ZMod q))^d*x^(f*r) = (Nat.fib a : FibAlg (ZMod q))^f * x^(d*s)*y^(f-d) := by
    apply (fib_root_unit.pow (d*f*t)).mul_left_inj.mp
    linear_combination hm
  have hxi : x*(x-1) = 1 := by dsimp [x]; linear_combination fib_root_sq (R := ZMod q)
  have he : (Nat.fib b : FibAlg (ZMod q))^d = (Nat.fib a : FibAlg (ZMod q))^f * modFibAlg q (obstruction r d s f) := by
    have hmul := congrArg (fun z : (FibAlg (ZMod q)) => z * (x-1)^(f*r)) hc
    simp only [obstruction,map_mul,map_pow,map_sub,map_one,map_ofNat,modFibAlg_omega]
    change _ = _ * ((x-1)^(f*r)*x^(d*s)*y^(f-d))
    calc
      _ = (Nat.fib b : FibAlg (ZMod q))^d * (x*(x-1))^(f*r) := by rw [hxi,one_pow,mul_one]
      _ = _ := by rw [mul_pow]; linear_combination hmul
  have he' := congrArg QuadraticAlgebra.im he
  have hv : (Nat.fib a : ZMod q)^f * (modFibAlg q (obstruction r d s f)).im = 0 := by
    simp only [← Nat.cast_pow,im_mul,im_natCast,re_natCast,zero_mul,mul_zero,add_zero] at he'
    simpa only [Nat.cast_pow] using he'.symm
  have hzero : (modFibAlg q (obstruction r d s f)).im = 0 := by
    apply ((hab a ha).pow f).mul_right_inj.mp
    simpa using hv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  exact_mod_cast Int.natAbs_dvd_natAbs.mpr hz

private theorem same_step_bound {q r s d t : ℕ} (hrs : r < s)
    (hr : q ∣ lucasFibonacciSum (r+d*t)) (hs : q ∣ lucasFibonacciSum (s+d*t)) :
    q ∣ Nat.fib (s-r) := by
  have hpos : 0 < lucasFibonacciSum (r+d*t) := by
    have := Nat.fib_pos.mpr (show 0 < r+d*t+2 by omega)
    unfold lucasFibonacciSum
    omega
  have : NeZero q := ⟨fun h => by simp [h] at hr; omega⟩
  apply common_divisor_lucasFibonacciSum_dvd_fib hr
  simpa only [show r+d*t+(s-r)=s+d*t by omega] using hs

/-- Along any two distinct affine index forms, all pointwise greatest common
divisors divide one positive integer depending only on the forms. -/
theorem affine_upper_gcd_bound (r d s f : ℕ) (hne : (r,d) ≠ (s,f)) :
    ∃ M > 0, ∀ t, (lucasFibonacciSum (r+d*t)).gcd (lucasFibonacciSum (s+f*t)) ∣ M := by
  have swap (a b c e M : ℕ) (h : ∀ t, (lucasFibonacciSum (a+b*t)).gcd (lucasFibonacciSum (c+e*t)) ∣ M) :
      ∀ t, (lucasFibonacciSum (c+e*t)).gcd (lucasFibonacciSum (a+b*t)) ∣ M :=
    fun t => by rw [Nat.gcd_comm]; exact h t
  have diff (a b c e : ℕ) (hlt : b < e) :
      ∀ t, (lucasFibonacciSum (a+b*t)).gcd (lucasFibonacciSum (c+e*t)) ∣ (obstruction a b c e).im.natAbs :=
    fun t => affine_common_dvd _ a b c e t hlt (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..)
  rcases lt_trichotomy d f with hl|rfl|hl
  · exact ⟨_,Int.natAbs_pos.mpr (obstruction_nonzero _ _ _ _ hl),diff _ _ _ _ hl⟩
  · have hne' : r ≠ s := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hne' with h|h
    · exact ⟨_,Nat.fib_pos.mpr (Nat.sub_pos_of_lt h),fun _ =>
        same_step_bound h (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..)⟩
    · exact ⟨_,Nat.fib_pos.mpr (Nat.sub_pos_of_lt h),swap _ _ _ _ _ (fun _ =>
        same_step_bound h (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..))⟩
  · exact ⟨_,Int.natAbs_pos.mpr (obstruction_nonzero _ _ _ _ hl),swap _ _ _ _ _ (diff _ _ _ _ hl)⟩

/-- Upper values at consecutive multiples of one index are coprime. -/
theorem consecutive_multiple_upper_coprime (k t : ℕ) :
    (lucasFibonacciSum (k*t)).Coprime (lucasFibonacciSum ((k+1)*t)) := by
  have hd := affine_common_dvd ((lucasFibonacciSum (k*t)).gcd (lucasFibonacciSum ((k+1)*t)))
    0 k 0 (k+1) t (by omega) (by simpa using Nat.gcd_dvd_left ..) (by simpa using Nat.gcd_dvd_right ..)
  apply Nat.dvd_one.mp
  simpa [obstruction] using hd

private theorem common_period_mod (M : ℕ) [NeZero M] :
    ∃ T > 0, ∀ r d t : ℕ,
      lucasFibonacciSum (r+d*(t+T)) ≡ lucasFibonacciSum (r+d*t) [MOD M] := by
  let : Finite (FibAlg (ZMod M)) := Finite.of_equiv _ (QuadraticAlgebra.equivProd (1:ZMod M) 1).symm
  let u := (fib_root_unit (R := ZMod M)).unit
  let T := orderOf u
  have hu : (ω : FibAlg (ZMod M))^T = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one u)
    change (u : FibAlg (ZMod M))^T = 1 at h
    rwa [show (u : FibAlg (ZMod M)) = ω from fib_root_unit.unit_spec] at h
  have coeff (n : ℕ) : scalarEval 4 ((ω : FibAlg (ZMod M))^n) = (lucasFibonacciSum n : ZMod M) := by
    rw [upper_power]
    simp [scalarEval]
    ring
  refine ⟨T,orderOf_pos u,fun r d t => ?_⟩
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  rw [← coeff,← coeff,show r+d*(t+T)=r+d*t+T*d by ring,pow_add,pow_mul,hu,one_pow,mul_one]

/-- The gcd sequence for two affine index forms has a positive period exactly
when the forms differ or both describe the same constant index. -/
theorem affine_upper_gcd_periodic_iff (r d s f : ℕ) :
    (∃ T > 0, Function.Periodic
      (fun t : ℕ => (lucasFibonacciSum (r+d*t)).gcd (lucasFibonacciSum (s+f*t))) T) ↔
      (r,d) ≠ (s,f) ∨ d=0 := by
  constructor
  · rintro ⟨T,hT,hper⟩
    by_contra! he
    obtain ⟨he,hd⟩ := he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    have h := hper 0
    simp only [zero_add,mul_zero,add_zero,Nat.gcd_self] at h
    have hi : r < r+d*T := Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.pos_of_ne_zero hd) hT)
    have hlt : lucasFibonacciSum r < lucasFibonacciSum (r+d*T) :=
      Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono hi.le)) (Nat.fib_add_two_strictMono hi)
    exact hlt.ne' h
  · intro hor
    by_cases he : (r,d) = (s,f)
    · have hd := hor.resolve_left (not_not.mpr he)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      subst_vars
      exact ⟨1,by decide,fun _ => by simp⟩
    · obtain ⟨M,hM,hbound⟩ := affine_upper_gcd_bound r d s f he
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨T,hT,hmod⟩ := common_period_mod M
      refine ⟨T,hT,fun t => Nat.dvd_antisymm ?_ ?_⟩
      · exact Nat.dvd_gcd (((hmod r d t).dvd_iff (hbound (t+T))).mp (Nat.gcd_dvd_left ..))
          (((hmod s f t).dvd_iff (hbound (t+T))).mp (Nat.gcd_dvd_right ..))
      · exact Nat.dvd_gcd (((hmod r d t).dvd_iff (hbound t)).mpr (Nat.gcd_dvd_left ..))
          (((hmod s f t).dvd_iff (hbound t)).mpr (Nat.gcd_dvd_right ..))

#print axioms affine_upper_gcd_periodic_iff
#print axioms affine_upper_gcd_bound
#print axioms consecutive_multiple_upper_coprime
end Arxiv.«2211.10788»
