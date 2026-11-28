import HosoyaRealEleven

/-! Cube norms at multiples of eighteen in the real quadratic ring of discriminant 44. -/

namespace Arxiv.«2211.10788».HosoyaCubeNorm
open RealEleven
open scoped RealEleven

private theorem twists {f y : ℤ} (hf : 2 ∣ f) (h : y^3+1=11*f^2) :
    ∃ (i : Fin 3) (v : RingEleven),
      (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^i.val*v^3 := by
  classical
  let := EuclideanDomain.gcdMonoid RingEleven
  let z : RingEleven := ⟨1,f⟩
  have hp : z * star z = (-(y:RingEleven))^3 := by
    rw [← Zsqrtd.norm_eq_mul_conj]
    have hn : z.norm=(-y)^3 := by
      change 1*1-11*f*f=(-y)^3
      linear_combination h
    rw [hn]; push_cast; rfl
  have tr : z+star z=2 := by ext <;> simp [z]
  have two : gcd z (star z) ∣ 2 := tr ▸ dvd_add (gcd_dvd_left ..) (gcd_dvd_right ..)
  obtain ⟨b,hb⟩ := hf
  have one : z-2*(⟨0,b⟩ : RingEleven)=1 := by ext <;> simp [z,hb]
  have cop := isUnit_of_dvd_one (one ▸ dvd_sub (gcd_dvd_left z (star z)) (dvd_mul_of_dvd_left two (⟨0,b⟩ : RingEleven)))
  obtain ⟨w,u,hw⟩ := exists_associated_pow_of_mul_eq_pow cop hp
  obtain ⟨n,hn⟩ := unit_signed_power u
  let k : ℤ := n/3
  let i : Fin 3 := ⟨(n%3).toNat,by omega⟩
  have hi : (i.val:ℤ)+k*3=n := by dsimp [i,k]; omega
  have hu : baseUnit^i.val * (baseUnit^k)^3 = baseUnit^n := by
    calc baseUnit^i.val * (baseUnit^k)^3 =
        baseUnit^(i.val:ℤ) * (baseUnit^k)^(3:ℤ) := by simp
      _ = _ := by rw [← zpow_mul,← zpow_add,hi]
  have he := congrArg (fun a : RingElevenˣ => (a:RingEleven)) hu
  simp only [Units.val_mul,Units.val_pow_eq_pow_val] at he
  let v := (↑(baseUnit^k):RingEleven)*w
  have hg : (baseUnit:RingEleven)^i.val*v^3 = (↑(baseUnit^n):RingEleven)*w^3 := by
    dsimp only [v]; rw [mul_pow,←mul_assoc,he]
  refine ⟨i,?_⟩
  rcases hn with hn|hn
  · exact ⟨v,by change z=_; rw [←hw,hn,mul_comm (w^3),hg]⟩
  · refine ⟨-v,?_⟩
    change z=_
    rw [←hw,hn]
    simp only [Units.val_neg,neg_pow,show (-1:RingEleven)^3 = -1 by norm_num]
    linear_combination hg

private def rePart {R : Type*} [CommRing R] (A B a b : R) :=
  A*(a^3+33*a*b^2)+11*B*(3*a^2*b+11*b^3)

private def imPart {R : Type*} [CommRing R] (A B a b : R) :=
  B*(a^3+33*a*b^2)+A*(3*a^2*b+11*b^3)

private theorem parts (A B a b : ℤ) :
    (⟨A,B⟩ : RingEleven)*(⟨a,b⟩ : RingEleven)^3 =
      ⟨rePart A B a b,imPart A B a b⟩ := by
  ext <;> simp [pow_succ,rePart,imPart] <;> ring

private theorem reject {A B a b f : ℤ} (h₁ : rePart A B a b=1) (h₂ : imPart A B a b=f)
    (hf : 9 ∣ f) (local_test : ∀ x y : ZMod 9, ¬(rePart (A:ZMod 9) B x y=1 ∧ imPart (A:ZMod 9) B x y=0)) : False := by
  have r := congrArg (fun n : ℤ => (n:ZMod 9)) h₁
  have s := congrArg (fun n : ℤ => (n:ZMod 9)) h₂
  simp only [rePart,imPart] at r s
  push_cast at r s
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd f 9).mpr hf] at s
  exact local_test a b ⟨r,s⟩

/-- At an integer multiple of eighteen, y³ + 1 = 11f² has only the solution f=0, y=−1. -/
theorem cube_norm_at_eighteen (f y : ℤ) (hf : 18 ∣ f) (h : y^3+1=11*f^2) :
    f=0 ∧ y= -1 := by
  obtain ⟨i,⟨a,b⟩,eqn⟩ := twists ((by decide : (2:ℤ) ∣ 18).trans hf) h
  have h₉ := (by decide : (9:ℤ) ∣ 18).trans hf
  fin_cases i
  · change (⟨1,f⟩ : RingEleven) = _ at eqn
    have e₀ : (baseUnit:RingEleven)^0 = ⟨1,0⟩ := by decide
    change (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^0 * _ at eqn
    rw [e₀,parts] at eqn
    have r := congrArg Zsqrtd.re eqn
    have s := congrArg Zsqrtd.im eqn
    change 1 = rePart 1 0 a b at r
    change f = imPart 1 0 a b at s
    have ha : a ∣ 1 := ⟨a^2+33*b^2,by rw [r]; dsimp [rePart]; ring⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ha) with rfl|rfl
    · have hb : b=0 := by dsimp [rePart] at r; nlinarith
      subst b; norm_num [imPart] at s; subst f
      constructor; · rfl
      have hz : (y+1)*(y^2-y+1)=0 := by linear_combination h
      rcases mul_eq_zero.mp hz with h|h
      · omega
      · nlinarith [sq_nonneg (2*y-1)]
    · dsimp [rePart] at r
      nlinarith [sq_nonneg b]
  · change (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^1 * _ at eqn
    rw [show (baseUnit:RingEleven)^1 = ⟨10,3⟩ by decide,parts] at eqn
    exact False.elim (reject (congrArg Zsqrtd.re eqn).symm (congrArg Zsqrtd.im eqn).symm h₉ (by decide))
  · change (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^2 * _ at eqn
    rw [show (baseUnit:RingEleven)^2 = ⟨199,60⟩ by decide,parts] at eqn
    exact False.elim (reject (congrArg Zsqrtd.re eqn).symm (congrArg Zsqrtd.im eqn).symm h₉ (by decide))

#print axioms cube_norm_at_eighteen

end Arxiv.«2211.10788».HosoyaCubeNorm
