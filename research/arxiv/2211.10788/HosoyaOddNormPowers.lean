import HosoyaOddPowerTrace
import LucasFibonacciOddCubes

/-! Odd powers of one plus eleven times a square. -/

namespace Arxiv.«2211.10788».HosoyaOddNorm
open QuadraticAlgebra ElevenRing

private def point (f : ℤ) : ElevenRing := ⟨1-f,2*f⟩

private lemma point_power {f y : ℤ} {p : ℕ} (hp : Odd p) (hf : Even f)
    (he : y^p=1+11*f^2) : ∃ w : ElevenRing, point f=w^p := by
  classical
  let := EuclideanDomain.gcdMonoid ElevenRing
  let z := point f
  have hn : z.norm=y^p := by simp [z,point,norm_def,he]; ring
  have hprod : z*star z=(y:ElevenRing)^p := by
    rw [←algebraMap_norm_eq_mul_star,hn,map_pow]; rfl
  have ht : z+star z=2 := by ext <;> simp [z,point]; ring
  have hd := gcd_dvd_left z (star z)
  have htwo : gcd z (star z) ∣ 2 := ht ▸ dvd_add hd (gcd_dvd_right ..)
  obtain ⟨c,hc⟩ := hf
  have h₁ : z-2*(⟨-c,2*c⟩ : ElevenRing)=1 := by ext <;> simp [z,point,hc] <;> ring
  have cop := isUnit_of_dvd_one (h₁ ▸ dvd_sub hd (dvd_mul_of_dvd_left htwo (⟨-c,2*c⟩ : ElevenRing)))
  obtain ⟨w,u,hw⟩ := exists_associated_pow_of_mul_eq_pow cop hprod
  have hi := unit_im_zero u
  have hu := Int.isUnit_iff.mp (u.isUnit.map (QuadraticAlgebra.norm : ElevenRing →* ℤ))
  have hn₁ : (u:ElevenRing).norm=1 := by have := norm_nonneg' (u:ElevenRing); omega
  rw [norm_def,hi] at hn₁
  have hr : (u:ElevenRing).re=1 ∨ (u:ElevenRing).re= -1 := by
    have : ((u:ElevenRing).re-1)*((u:ElevenRing).re+1)=0 := by nlinarith
    rcases mul_eq_zero.mp this with h|h <;> omega
  rcases hr with h|h
  · have hunit : (u:ElevenRing)=1 := QuadraticAlgebra.ext h hi
    exact ⟨w,by simpa [hunit,z] using hw.symm⟩
  · have hunit : (u:ElevenRing)= -1 := by ext <;> simp [h,hi]
    exact ⟨-w,by simpa [hunit,z,hp.neg_pow] using hw.symm⟩

private abbrev Residue := QuadraticAlgebra (ZMod 2) (-3) 1

private def reduceTwo : ElevenRing →+* Residue where
  toFun x := ⟨x.re,x.im⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private lemma odd_root_mod_two {w : ElevenRing} {p : ℕ} (hp : p.Prime) (h₃ : p≠3)
    (he : reduceTwo w^p=1) : reduceTwo w=1 := by
  let z := reduceTwo w
  have hz : z≠0 := by intro h; change z^p=1 at he; simp [h,zero_pow hp.ne_zero] at he
  have cube : z^3=1 := by
    obtain ⟨a,b⟩ := z
    exact (by decide : ∀ a b : ZMod 2, (⟨a,b⟩:Residue)≠0 → (⟨a,b⟩:Residue)^3=1) a b hz
  apply orderOf_eq_one_iff.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he) (orderOf_dvd_of_pow_eq_one cube)
  have cop : p.Coprime 3 := (Nat.coprime_primes hp (by decide)).mpr h₃
  exact Nat.eq_one_of_dvd_one (cop.gcd_eq_one ▸ hd)

private def embed : Zsqrtd (-11) →+* ElevenRing where
  toFun x := ⟨x.re-x.im,2*x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp [Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

private lemma embed_injective : Function.Injective embed := by
  intro x y he
  have ha := congrArg QuadraticAlgebra.re he
  have hb := congrArg QuadraticAlgebra.im he
  change x.re-x.im=y.re-y.im at ha
  change 2*x.im=2*y.im at hb
  exact Zsqrtd.ext (by omega) (by omega)

private lemma real_dvd_odd {a b : ℤ} {p : ℕ} (hp : Odd p) :
    a ∣ ((⟨a,b⟩ : Zsqrtd (-11))^p).re := by
  let z : Zsqrtd (-11) := ⟨a,b⟩
  have hi (s : ℕ) : a ∣ (z^(2*s)).im := by
    induction s with
    | zero => simp
    | succ s hs =>
      rw [Nat.mul_succ,pow_add,Zsqrtd.im_mul]
      apply dvd_add
      · have hsq : (z^2).im=2*a*b := by simp [sq,z,Zsqrtd.im_mul]; ring
        rw [hsq]
        exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left ..) _) _
      · exact dvd_mul_of_dvd_left hs _
  obtain ⟨s,rfl⟩ := hp
  change a ∣ (z^(2*s+1)).re
  rw [pow_succ,Zsqrtd.re_mul]
  exact dvd_add (dvd_mul_left ..) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hi s) _) _)

private def reduceEleven : Zsqrtd (-11) →+* ZMod 11 where
  toFun x := x.re
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by simp
  map_mul' x y := by simp [Zsqrtd.re_mul,show (11:ZMod 11)=0 by decide]

private lemma cubic_point {f : ℤ} {w : ElevenRing} (he : point f=w^3) : f=0 := by
  let a := 2*w.re+w.im
  have ht := congrArg (fun x : ElevenRing => 2*x.re+x.im) he
  have eqn : a*(a^2-33*w.im^2)=8 := by
    simp [point,pow_succ] at ht
    dsimp [a]
    linear_combination -4*ht
  have hdm : a.natAbs ∣ 8 := Int.natAbs_dvd_natAbs.mpr (show a ∣ (8:ℤ) from ⟨_,eqn.symm⟩)
  have hbound := Nat.le_of_dvd (by decide : 0<8) hdm
  have hm := congrArg (Int.castRingHom (ZMod 11)) eqn
  have hc : (a:ZMod 11)^3=8 := by
    have h33 : (33:ZMod 11)=0 := by decide
    simpa [h33,pow_succ,mul_assoc] using hm
  have ha : (a:ZMod 11)=2 := (by decide : ∀ t : ZMod 11, t^3=8 → t=2) _ hc
  have hd : (11:ℤ) ∣ a-2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (by simp [ha])
  have ha₂ : a=2 := by omega
  rw [ha₂] at eqn
  have hb : w.im=0 := by nlinarith [sq_nonneg w.im]
  have hr : w.re=1 := by dsimp [a] at ha₂; omega
  rw [show w=1 from QuadraticAlgebra.ext hr hb,one_pow] at he
  have hi := congrArg QuadraticAlgebra.im he
  change 2*f=0 at hi
  omega

private lemma prime_point {f : ℤ} {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hf : Even f) {w : ElevenRing} (he : point f=w^p) : f=0 := by
  by_cases h₃ : p=3
  · exact cubic_point (h₃ ▸ he)
  obtain ⟨s,hs⟩ := hf
  have hz : reduceTwo (point f)=1 := by
    have h₂ : (f:ZMod 2)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr ⟨s,by omega⟩
    apply QuadraticAlgebra.ext
    · change ((1-f:ℤ):ZMod 2)=1
      simp [h₂]
    · change ((2*f:ℤ):ZMod 2)=0
      simp [h₂]
  have hw := odd_root_mod_two hp h₃ (by rwa [he,map_pow] at hz)
  have hr := congrArg QuadraticAlgebra.re hw
  have hi := congrArg QuadraticAlgebra.im hw
  change (w.re:ZMod 2)=1 at hr
  change (w.im:ZMod 2)=0 at hi
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hi
  let a := w.re+b
  let z : Zsqrtd (-11) := ⟨a,b⟩
  have hmap : embed z=w := QuadraticAlgebra.ext (by change a-b=_; dsimp [a]; omega) (by change 2*b=w.im; exact hb.symm)
  have heq : (⟨1,f⟩ : Zsqrtd (-11))=z^p := by
    apply embed_injective
    rw [map_pow,hmap]
    exact he
  have hreal := congrArg Zsqrtd.re heq
  change 1=(z^p).re at hreal
  have hau : a ∣ 1 := hreal.symm ▸ real_dvd_odd (a:=a) (b:=b) ho
  have ha : a=1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hau) with h|h
    · exact h
    · have hz₁ := congrArg reduceEleven heq
      rw [map_pow] at hz₁
      change (1:ZMod 11)=(a:ZMod 11)^p at hz₁
      rw [h,Int.cast_neg,Int.cast_one,ho.neg_one_pow] at hz₁
      exact False.elim ((by decide : (1:ZMod 11)≠ -1) hz₁)
  have hb₀ : (b:ZMod 2)=0 := by
    have ha' : w.re+b=1 := ha
    have hc := congrArg (Int.castRingHom (ZMod 2)) ha'
    simpa [hr] using hc
  obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hb₀
  have hc₀ : c=0 := real_part_odd_power_eq_one (d:= -11) (by decide) ho hp.one_lt
    (by simpa [z,ha,hc] using hreal.symm)
  have hz₁ : z=1 := by ext <;> simp [z,ha,hc,hc₀]
  rw [hz₁,one_pow] at heq
  exact congrArg Zsqrtd.im heq

private lemma even_of_norm_power {f y : ℤ} {p : ℕ} (hp : 3 ≤ p) (he : y^p=1+11*f^2) :
    Even f := by
  by_contra hf
  obtain ⟨s,hs⟩ := Int.not_even_iff_odd.mp hf
  have h₂ : (2:ℤ) ∣ y^p := ⟨22*s^2+22*s+6,by rw [he,hs]; ring⟩
  have hy := Int.prime_two.dvd_of_dvd_pow h₂
  have h₈ : (8:ℤ) ∣ y^p := pow_dvd_pow_of_dvd_of_le hy hp
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (y^p) 8).mpr h₈
  rw [he,hs] at hz
  push_cast at hz
  exact (by decide : ∀ s : ZMod 8, 1+11*(2*s+1)^2 ≠ 0) _ hz

/-- The coefficient-eleven case of the odd-power equation treated by Nagell
and Cohn. For every odd exponent greater than one, equality forces f=0. -/
theorem odd_power_eq_one_add_eleven_square {f y : ℤ} {n : ℕ} (hn : 1<n) (ho : Odd n)
    (he : y^n=1+11*f^2) : f=0 := by
  obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hp₂ : p≠2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpn)
  have hp₃ : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨k,hk⟩ := hpn
  have he' : (y^k)^p=1+11*f^2 := by simpa [←pow_mul,Nat.mul_comm k p,←hk] using he
  have hf := even_of_norm_power hp₃ he'
  obtain ⟨w,hw⟩ := point_power (hp.odd_of_ne_two hp₂) hf he'
  exact prime_point hp (hp.odd_of_ne_two hp₂) hf hw

#print axioms odd_power_eq_one_add_eleven_square

end Arxiv.«2211.10788».HosoyaOddNorm
