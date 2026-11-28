import HosoyaRealEleven

/-! Odd powers and split-prime obstructions in the real quadratic ring ℤ[√11]. -/

namespace Arxiv.«2211.10788».HosoyaAuxiliaryPrime

open RealEleven
open scoped RealEleven

/-- For an odd exponent the unit exponent can be chosen in a single residue period. -/
theorem odd_norm_unit_twists {p : ℕ} (hp : Odd p) {f y : ℤ} (hf : 2 ∣ f)
    (h : y^p+1 = 11*f^2) :
    ∃ (i : Fin p) (v : RingEleven),
      (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^i.val*v^p := by
  classical
  let := EuclideanDomain.gcdMonoid RingEleven
  let z : RingEleven := ⟨1,f⟩
  have hp₀ : 0 < p := hp.pos
  have hpi : 0 < (p:ℤ) := by exact_mod_cast hp₀
  have hn : z.norm = (-y)^p := by
    rw [hp.neg_pow]
    change 1*1-11*f*f = -(y^p)
    linear_combination h
  have hz : z * star z = (-(y:RingEleven))^p := by
    rw [← Zsqrtd.norm_eq_mul_conj,hn]
    push_cast
    rfl
  have tr : z+star z=2 := by ext <;> simp [z]
  have two : gcd z (star z) ∣ 2 := tr ▸ dvd_add (gcd_dvd_left ..) (gcd_dvd_right ..)
  obtain ⟨b,hb⟩ := hf
  have one : z-2*(⟨0,b⟩ : RingEleven)=1 := by ext <;> simp [z,hb]
  have cop := isUnit_of_dvd_one (one ▸ dvd_sub (gcd_dvd_left z (star z))
    (dvd_mul_of_dvd_left two (⟨0,b⟩ : RingEleven)))
  obtain ⟨w,u,hw⟩ := exists_associated_pow_of_mul_eq_pow cop hz
  obtain ⟨n,hn⟩ := unit_signed_power u
  have h₀ := Int.emod_nonneg n hpi.ne'
  have h₁ := Int.emod_lt_of_pos n hpi
  let i : Fin p := ⟨(n%p).toNat,by omega⟩
  let k : ℤ := n/p
  have hi : (i.val:ℤ)+k*p=n := by
    dsimp [i,k]
    rw [Int.toNat_of_nonneg h₀,mul_comm]
    exact Int.emod_add_mul_ediv n p
  have hu : baseUnit^i.val * (baseUnit^k)^p = baseUnit^n := by
    calc baseUnit^i.val * (baseUnit^k)^p =
        baseUnit^(i.val:ℤ) * (baseUnit^k)^(p:ℤ) := by simp
      _ = _ := by rw [← zpow_mul,← zpow_add,hi]
  have he := congrArg (fun a : RingElevenˣ => (a:RingEleven)) hu
  simp only [Units.val_mul,Units.val_pow_eq_pow_val] at he
  let v := (↑(baseUnit^k):RingEleven)*w
  have hg : (baseUnit:RingEleven)^i.val*v^p = (↑(baseUnit^n):RingEleven)*w^p := by
    dsimp only [v]; rw [mul_pow,←mul_assoc,he]
  refine ⟨i,?_⟩
  rcases hn with hn|hn
  · exact ⟨v,by change z=_; rw [←hw,hn,mul_comm (w^p),hg]⟩
  · refine ⟨-v,?_⟩
    change z=_
    rw [←hw,hn,hp.neg_pow]
    simp only [Units.val_neg]
    linear_combination hg

private lemma odd_coordinates (a b : ℤ) (hb : b ≠ 0) (t : ℕ) :
    ∃ A B : ℤ, 0 < A ∧ 0 < B ∧ (0 < t → 1 < A) ∧
      (⟨a,b⟩ : RingEleven)^(2*t+1) = ⟨a*A,b*B⟩ := by
  have hs : 1 ≤ b^2 := by nlinarith [sq_pos_of_ne_zero hb]
  induction t with
  | zero => exact ⟨1,1,by decide,by decide,by omega,by simp⟩
  | succ t ih =>
    obtain ⟨A,B,hA,hB,_,he⟩ := ih
    let T := a^2+11*b^2
    have hT : 1 < T := by dsimp [T]; nlinarith [sq_nonneg a]
    have hA' : 1 < A*T+22*b^2*B := by
      nlinarith [Int.mul_le_mul_of_nonneg_right (show 1 ≤ A by omega) (show 0 ≤ T by omega),
        mul_nonneg (sq_nonneg b) hB.le]
    have hB' : 0 < 2*a^2*A+B*T := by positivity
    refine ⟨A*T+22*b^2*B,2*a^2*A+B*T,by omega,hB',fun _ => hA',?_⟩
    rw [show 2*(t+1)+1=(2*t+1)+2 by omega,pow_add,he]
    ext <;> simp [pow_two,T] <;> ring

/-- A pure odd power with real component one has zero irrational component. -/
theorem pure_power {p : ℕ} (hp : Odd p) (hp₁ : 1 < p) {f : ℤ} {v : RingEleven}
    (he : (⟨1,f⟩ : RingEleven) = v^p) : f=0 := by
  obtain ⟨a,b⟩ := v
  by_cases hb : b=0
  · subst b
    change (⟨1,f⟩ : RingEleven) = (a:RingEleven)^p at he
    rw [←Int.cast_pow] at he
    exact congrArg Zsqrtd.im he
  obtain ⟨t,ht⟩ := hp
  obtain ⟨A,B,hA,hB,hs,hc⟩ := odd_coordinates a b hb t
  rw [ht,hc] at he
  have h : 1=a*A := congrArg Zsqrtd.re he
  have unit : IsUnit A := isUnit_of_dvd_one ⟨a,by linarith [mul_comm a A]⟩
  have hbig := hs (by omega)
  rcases Int.isUnit_iff.mp unit with h'|h' <;> omega

/-- At a split prime q with q−1=pk, every nonzero specialization of 1+f√11
has its k-th power determined by the same global unit exponent. -/
theorem residue_of_twist {q p k : ℕ} [Fact q.Prime] (hk : p*k=q-1)
    {r : ZMod q} (hr : r*r=11) {i : ℕ} {v : RingEleven} {f : ℤ}
    (he : (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^i*v^p) :
    1+(f:ZMod q)*r=0 ∨ (1+(f:ZMod q)*r)^k=((10+3*r)^k)^i := by
  let σ : RingEleven →+* ZMod q := Zsqrtd.lift ⟨r, by simpa using hr⟩
  have eqn := congrArg σ he
  simp only [map_mul,map_pow] at eqn
  have hl : σ ⟨1,f⟩=1+(f:ZMod q)*r := by simp [σ,Zsqrtd.lift_apply_apply]
  have hu : σ (baseUnit:RingEleven)=10+3*r := by simp [σ,Zsqrtd.lift_apply_apply]
  rw [hl,hu] at eqn
  by_cases hz : σ v=0
  · left
    have hqp := (Fact.out : Nat.Prime q).two_le
    have hn : p≠0 := by intro h; simp [h] at hk; omega
    simp [eqn,hz,zero_pow hn]
  · right
    rw [eqn,mul_pow,←pow_mul (σ v),hk,ZMod.pow_card_sub_one_eq_one hz,mul_one]
    rw [←pow_mul,←pow_mul,Nat.mul_comm i k]

/-- Tests both reductions √11 ↦ ±r of the same algebraic integer. -/
def Compatible {q : ℕ} (k : ℕ) (r f : ZMod q) (i : ℕ) : Prop :=
  (1+f*r=0 ∨ (1+f*r)^k=((10+3*r)^k)^i) ∧
  (1-f*r=0 ∨ (1-f*r)^k=((10-3*r)^k)^i)

instance {q : ℕ} (k : ℕ) (r f : ZMod q) (i : ℕ) : Decidable (Compatible k r f i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem compatible_of_twist {q p k : ℕ} [Fact q.Prime] (hk : p*k=q-1)
    {r : ZMod q} (hr : r*r=11) {i : ℕ} {v : RingEleven} {f : ℤ}
    (he : (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^i*v^p) :
    Compatible k r f i := by
  refine ⟨residue_of_twist hk hr he,?_⟩
  have hs : (-r)*(-r)=11 := by simpa using hr
  simpa only [mul_neg,←sub_eq_add_neg] using residue_of_twist hk hs he

#print axioms compatible_of_twist

#print axioms odd_norm_unit_twists
#print axioms pure_power

end Arxiv.«2211.10788».HosoyaAuxiliaryPrime
