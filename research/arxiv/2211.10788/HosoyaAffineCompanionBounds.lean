import HosoyaCriticalCompanionLifts

/-! Common prime powers in the two companion coordinates at distinct affine indices. -/

namespace Arxiv.«2211.10788».LocalPower.CompanionAffine

open QuadraticAlgebra
private abbrev FibAlg (R : Type*) [CommRing R] := QuadraticAlgebra R 1 1

private theorem fib_root_sq {R : Type*} [CommRing R] :
    (ω : FibAlg R)^2 = ω + 1 := by
  rw [pow_two,omega_mul_omega_eq_add]
  simp [add_comm]

private theorem fib_root_unit {R : Type*} [CommRing R] : IsUnit (ω : FibAlg R) := by
  apply IsUnit.of_mul_eq_one (ω-1)
  linear_combination fib_root_sq (R := R)

private theorem coordinate_power (R : Type*) [CommRing R] (n : ℕ) :
    (ω : FibAlg R)^n = (Nat.fib (n+1) : FibAlg R)*(7*ω-6) + (coordinate n : FibAlg R)*(1-ω) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show coordinate 0=7 by decide]
    norm_num
    ring
  | one =>
    rw [show coordinate 1=6 by decide]
    norm_num
    ring
  | more n h₀ h₁ =>
    rw [pow_add, fib_root_sq, mul_add, mul_one, ← pow_succ, h₁,h₀]
    rw [show n+2+1=(n+1)+2 by omega,Nat.fib_add_two (n:=n+1),coordinate_rec]
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
  (ω-1)^(f*r) * ω^(d*s) * (7*ω-6)^(f-d)

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
      e x = (e ω-1)^(f*r)*(e ω)^(d*s)*(7*e ω-6)^(f-d) := by
    simp only [x,obstruction,map_mul,map_pow,map_sub,map_one,map_ofNat,modFibAlg_omega]
  have he₁ : e₁ ω = 4 := by simp [e₁,rootEval,scalarEval]
  have he₂ : e₂ ω = -3 := by simp [e₂,rootEval,scalarEval]
  rw [home,home,he₁,he₂] at ee
  rw [show 7*(4:ZMod 11)-6=0 by decide,zero_pow (Nat.sub_ne_zero_of_lt h),mul_zero] at ee
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by decide : (-3:ZMod 11)-1 ≠ 0))
    (pow_ne_zero _ (by decide : (-3:ZMod 11) ≠ 0))) (pow_ne_zero _ (by decide : 7*(-3:ZMod 11)-6 ≠ 0))) ee.symm

private theorem affine_common_dvd (q r d s f t : ℕ) (hdf : d < f)
    (ha : q ∣ (coordinate (r+d*t)).natAbs) (hb : q ∣ (coordinate (s+f*t)).natAbs) :
    q ∣ (obstruction r d s f).im.natAbs := by
  let a := r+d*t
  let b := s+f*t
  let x := (ω : FibAlg (ZMod q))
  let y := 7*x-6
  have hpow (n : ℕ) (hh : q ∣ (coordinate n).natAbs) :
      x^n = (Nat.fib (n+1) : FibAlg (ZMod q))*y := by
    have hd : (q:ℤ) ∣ coordinate n := Int.natAbs_dvd_natAbs.mp (by simpa using hh)
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hd
    have hz' := congrArg (algebraMap (ZMod q) (FibAlg (ZMod q))) hz
    simp only [map_intCast,map_zero] at hz'
    simpa only [hz',zero_mul,add_zero] using coordinate_power (ZMod q) n
  have hab (n : ℕ) (hh : q ∣ (coordinate n).natAbs) :
      IsUnit (Nat.fib (n+1) : ZMod q) := by
    have hh' := hpow n hh
    have hu : IsUnit (Nat.fib (n+1) : FibAlg (ZMod q)) :=
      isUnit_of_mul_isUnit_left (hh' ▸ (fib_root_unit.pow n))
    obtain ⟨z,hz⟩ := isUnit_iff_exists_inv.mp hu
    apply IsUnit.of_mul_eq_one z.re
    simpa using congrArg QuadraticAlgebra.re hz
  have hm : (Nat.fib (b+1) : FibAlg (ZMod q))^d*x^(f*a) =
      (Nat.fib (a+1) : FibAlg (ZMod q))^f * x^(d*b)*y^(f-d) := by
    rw [Nat.mul_comm f a,Nat.mul_comm d b,pow_mul,pow_mul,hpow a ha,hpow b hb,mul_pow,mul_pow]
    rw [show f = d + (f-d) by omega]
    simp only [pow_add,Nat.add_sub_cancel_left]
    ring
  have he₁ : f*a = f*r+d*f*t := by dsimp [a]; ring
  have he₂ : d*b = d*s+d*f*t := by dsimp [b]; ring
  rw [he₁,he₂,pow_add,pow_add] at hm
  have hc : (Nat.fib (b+1) : FibAlg (ZMod q))^d*x^(f*r) = (Nat.fib (a+1) : FibAlg (ZMod q))^f * x^(d*s)*y^(f-d) := by
    apply (fib_root_unit.pow (d*f*t)).mul_left_inj.mp
    linear_combination hm
  have hxi : x*(x-1) = 1 := by dsimp [x]; linear_combination fib_root_sq (R := ZMod q)
  have he : (Nat.fib (b+1) : FibAlg (ZMod q))^d = (Nat.fib (a+1) : FibAlg (ZMod q))^f * modFibAlg q (obstruction r d s f) := by
    have hmul := congrArg (fun z : (FibAlg (ZMod q)) => z * (x-1)^(f*r)) hc
    simp only [obstruction,map_mul,map_pow,map_sub,map_one,map_ofNat,modFibAlg_omega]
    change _ = _ * ((x-1)^(f*r)*x^(d*s)*y^(f-d))
    calc
      _ = (Nat.fib (b+1) : FibAlg (ZMod q))^d * (x*(x-1))^(f*r) := by rw [hxi,one_pow,mul_one]
      _ = _ := by rw [mul_pow]; linear_combination hmul
  have he' := congrArg QuadraticAlgebra.im he
  have hv : (Nat.fib (a+1) : ZMod q)^f * (modFibAlg q (obstruction r d s f)).im = 0 := by
    simp only [← Nat.cast_pow,im_mul,im_natCast,re_natCast,zero_mul,mul_zero,add_zero] at he'
    simpa only [Nat.cast_pow] using he'.symm
  have hzero : (modFibAlg q (obstruction r d s f)).im = 0 := by
    apply ((hab a ha).pow f).mul_right_inj.mp
    simpa using hv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  exact_mod_cast Int.natAbs_dvd_natAbs.mpr hz

private theorem same_step_bound {q r s d t : ℕ} (hrs : r<s)
    (hr : q ∣ (coordinate (r+d*t)).natAbs) (hs : q ∣ (coordinate (s+d*t)).natAbs) :
    q ∣ 22*Nat.fib (s-r) := by
  let n := r+d*t
  let j := s-r
  have h₀ : (q:ℤ) ∣ coordinate n := Int.natAbs_dvd_natAbs.mp (by simpa [n] using hr)
  have h₁ : (q:ℤ) ∣ coordinate (n+j) := Int.natAbs_dvd_natAbs.mp (by
    simpa [n,j,show r+d*t+(s-r)=s+d*t by omega] using hs)
  have eq := cross_coordinate n j
  have z : (q:ℤ) ∣ -22*(-1:ℤ)^n*Nat.fib j := eq ▸ dvd_sub (dvd_mul_of_dvd_right h₁ _) (dvd_mul_of_dvd_left h₀ _)
  simpa [Int.natAbs_mul,Int.natAbs_pow,j] using Int.natAbs_dvd_natAbs.mpr z

/-- Along any two distinct affine index forms, all pointwise greatest common
divisors divide one positive integer depending only on the forms. -/
theorem affine_companion_gcd_bound (r d s f : ℕ) (hne : (r,d) ≠ (s,f)) :
    ∃ M > 0, ∀ t, ((coordinate (r+d*t)).natAbs).gcd ((coordinate (s+f*t)).natAbs) ∣ M := by
  have swap (a b c e M : ℕ) (h : ∀ t, ((coordinate (a+b*t)).natAbs).gcd ((coordinate (c+e*t)).natAbs) ∣ M) :
      ∀ t, ((coordinate (c+e*t)).natAbs).gcd ((coordinate (a+b*t)).natAbs) ∣ M :=
    fun t => by rw [Nat.gcd_comm]; exact h t
  have diff (a b c e : ℕ) (hlt : b < e) :
      ∀ t, ((coordinate (a+b*t)).natAbs).gcd ((coordinate (c+e*t)).natAbs) ∣ (obstruction a b c e).im.natAbs :=
    fun t => affine_common_dvd _ a b c e t hlt (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..)
  rcases lt_trichotomy d f with hl|rfl|hl
  · exact ⟨_,Int.natAbs_pos.mpr (obstruction_nonzero _ _ _ _ hl),diff _ _ _ _ hl⟩
  · have hne' : r ≠ s := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hne' with h|h
    · exact ⟨_,Nat.mul_pos (by decide : 0<22) (Nat.fib_pos.mpr (Nat.sub_pos_of_lt h)),fun _ =>
        same_step_bound h (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..)⟩
    · exact ⟨_,Nat.mul_pos (by decide : 0<22) (Nat.fib_pos.mpr (Nat.sub_pos_of_lt h)),swap _ _ _ _ _ (fun _ =>
        same_step_bound h (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..))⟩
  · exact ⟨_,Int.natAbs_pos.mpr (obstruction_nonzero _ _ _ _ hl),swap _ _ _ _ _ (diff _ _ _ _ hl)⟩

#print axioms affine_companion_gcd_bound

end Arxiv.«2211.10788».LocalPower.CompanionAffine
