import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciIndexForms
import research.arxiv.«2211.10788».LucasFibonacciPrimePowerLifts

/-! Fixed divisors of the homogeneous forms for the upper Hosoya diagonal. -/

namespace Arxiv.«2211.10788»

private abbrev FibAlg (R : Type*) [CommRing R] := QuadraticAlgebra R 1 1

/-- Evaluation of the index form as a linear functional on the quadratic power. -/
theorem upperIndexForm_power {R : Type*} [CommRing R] (x y : R) (d r : ℕ) :
    upperIndexForm x y d r =
      (lucasFibonacciSum r:R)*((⟨x,y⟩:QuadraticAlgebra R 1 1)^d).re +
      (lucasFibonacciSum (r+1):R)*((⟨x,y⟩:QuadraticAlgebra R 1 1)^d).im := by
  induction d generalizing r with
  | zero => simp [upperIndexForm,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  | succ d ih =>
    simp only [upperIndexForm,ih,pow_succ,lucas_fibonacci_sum_recurrence,
      Nat.cast_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
    ring

private lemma scalar_powers_inert {p d : ℕ} (hp : p.Prime) (hd : 0<d)
    (hi : ∀ a : ZMod p, a^2 ≠ 1+1*a) :
    (∀ z : FibAlg (ZMod p), (z^d).im=0) ↔ p+1 ∣ d := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (∀ a : ZMod p, a^2 ≠ 1+1*a) := ⟨hi⟩
  let K := FibAlg (ZMod p)
  let : Finite K := Finite.of_equiv _ (QuadraticAlgebra.equivProd (1:ZMod p) 1).symm
  let : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have scalar (z : K) : z.im=0 ↔ z^p=z := by
    rw [← Subfield.mem_bot_iff_pow_eq_self K p, mem_bot_iff_intCast p K]
    constructor
    · intro h
      obtain ⟨n,hn⟩ := ZMod.intCast_surjective z.re
      exact ⟨n,QuadraticAlgebra.ext hn (by exact h.symm)⟩
    · rintro ⟨n,rfl⟩
      rfl
  have unit (u : Kˣ) : ((u:K)^d).im=0 ↔ u^(d*(p-1))=1 := by
    rw [scalar,pow_mul]
    have h : p=p-1+1 := by have := hp.two_le; omega
    rw [show ((u:K)^d)^p=((u:K)^d)^(p-1)*((u:K)^d) from
      (congrArg (fun j : ℕ => ((u:K)^d)^j) h).trans (pow_succ ..)]
    rw [mul_eq_right₀ (pow_ne_zero _ u.ne_zero),←Units.val_inj]
    simp
  have card : Nat.card Kˣ=(p+1)*(p-1) := by
    rw [Nat.card_units,Nat.card_congr (QuadraticAlgebra.equivProd (1:ZMod p) 1),
      Nat.card_prod,Nat.card_zmod]
    have := hp.two_le
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    simp
    rw [show (q+1)*(q+1)=(q+1+1)*q+1 by ring]
    omega
  have hpos : 0<p-1 := by have := hp.two_le; omega
  constructor
  · intro h
    obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α:=Kˣ)
    have hh := orderOf_dvd_of_pow_eq_one ((unit g).mp (h g))
    rw [hg,card] at hh
    exact (Nat.dvd_of_mul_dvd_mul_right hpos hh)
  · intro h z
    by_cases hz : z=0
    · simp [hz,zero_pow hd.ne']
    let u : Kˣ := Units.mk0 z hz
    apply (unit u).mpr
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_natCard u).trans
    rw [card]
    exact mul_dvd_mul_right h _


private lemma eval_power {R : Type*} [CommRing R] (a : R) (ha : a^2=1+a)
    (z : FibAlg R) (d : ℕ) :
    (z^d).re+a*(z^d).im=(z.re+a*z.im)^d := by
  induction d with
  | zero => simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  | succ d ih =>
    rw [pow_succ,pow_succ,←ih,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
    linear_combination -(z^d).im*z.im*ha

private lemma scalar_powers_split {p d : ℕ} (hp : p.Prime) (h5 : p ≠ 5)
    (hd : 0<d) {a : ZMod p} (ha : a^2=1+a) :
    ¬∀ z : FibAlg (ZMod p), (z^d).im=0 := by
  let : Fact p.Prime := ⟨hp⟩
  let b := 1-a
  have hb : b^2=1+b := by dsimp [b]; linear_combination ha
  have hab : b-a ≠ 0 := by
    have h : (b-a)^2=5 := by dsimp [b]; linear_combination 4*ha
    intro he
    rw [he,zero_pow (by decide)] at h
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
      ((ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h.symm)))
  let z : FibAlg (ZMod p) := ⟨-a,1⟩
  intro hall
  have h₁ := eval_power a ha z d
  have h₂ := eval_power b hb z d
  rw [hall z,mul_zero,add_zero] at h₁ h₂
  have hz : (z^d).re=0 := by simpa [z,hd.ne'] using h₁
  rw [hz] at h₂
  exact (pow_ne_zero d hab) (by simpa [z,sub_eq_neg_add] using h₂.symm)

/-- Residue classes where the Fibonacci quadratic is irreducible over the prime field. -/
theorem fibonacci_nonsplit_mod_five {p : ℕ} (hp : p.Prime) (h5 : p≠5) :
    (∀ a : ZMod p, a^2 ≠ 1+1*a) ↔ p%5=2 ∨ p%5=3 := by
  by_cases h2 : p=2
  · subst p
    decide
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have two : (2:ZMod p)≠0 := by
    have h := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).not.mpr h2
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr h
  have root : (∃ a : ZMod p, a^2=1+1*a) ↔ IsSquare (5:ZMod p) := by
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨2*a-1,by linear_combination -4*ha⟩
    · rintro ⟨z,hz⟩
      exact ⟨(1+z)/2,by field_simp; linear_combination -hz⟩
  rw [←not_exists,root]
  have qr := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=5) (q:=p) (by decide) h2
  have hs : IsSquare (5:ZMod p) ↔ IsSquare (p:ZMod 5) := qr.symm
  rw [hs]
  have hres (z : ZMod 5) : ¬IsSquare z ↔ z.val=2 ∨ z.val=3 := by
    revert z
    decide
  simpa using hres (p:ZMod 5)

private lemma coprime_next (r : ℕ) : (lucasFibonacciSum r).Coprime (lucasFibonacciSum (r+1)) := by
  induction r with
  | zero => simp [lucas_fibonacci_sum_zero]
  | succ r ih =>
    rw [show r+1+1=r+2 by omega,lucas_fibonacci_sum_recurrence,Nat.coprime_self_add_right]
    exact ih.symm

private lemma form_cast (m : ℕ) (x y : ℤ) (d r : ℕ) :
    ((upperIndexForm x y d r:ℤ):ZMod m)=upperIndexForm (x:ZMod m) (y:ZMod m) d r := by
  induction d generalizing r with
  | zero => simp [upperIndexForm]
  | succ d ih => simp [upperIndexForm,ih]

private lemma fixed_iff_scalar (m r d : ℕ) :
    (∀ x y : ℤ, (m:ℤ) ∣ upperIndexForm x y d r) ↔
    m ∣ lucasFibonacciSum r ∧ ∀ z : FibAlg (ZMod m), (z^d).im=0 := by
  have equiv : (∀ x y : ℤ, (m:ℤ) ∣ upperIndexForm x y d r) ↔
      ∀ x y : ZMod m, upperIndexForm x y d r=0 := by
    constructor
    · intro h x y
      obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨b,rfl⟩ := ZMod.intCast_surjective y
      rw [←form_cast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (h a b)
    · intro h x y
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
      rw [form_cast]
      exact h _ _
  rw [equiv]
  constructor
  · intro h
    have hu : (lucasFibonacciSum r:ZMod m)=0 := by
      have h₁ := h 1 0
      rw [upperIndexForm_power,show (⟨1,0⟩:FibAlg (ZMod m))=1 from rfl,one_pow] at h₁
      simpa [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] using h₁
    have hm := (ZMod.natCast_eq_zero_iff ..).mp hu
    refine ⟨hm,?_⟩
    have unit : IsUnit (lucasFibonacciSum (r+1):ZMod m) :=
      (ZMod.isUnit_iff_coprime ..).mpr ((coprime_next r).of_dvd_left hm).symm
    rintro ⟨x,y⟩
    have hz := h x y
    rw [upperIndexForm_power,hu,zero_mul,zero_add] at hz
    exact unit.mul_right_eq_zero.mp hz
  · rintro ⟨hu,h⟩ x y
    rw [upperIndexForm_power,(ZMod.natCast_eq_zero_iff ..).mpr hu,h,zero_mul,mul_zero,add_zero]


private def reducePair (m : ℕ) : FibAlg ℤ →+* FibAlg (ZMod m) where
  toFun z := ⟨z.re,z.im⟩
  map_zero' := by ext <;> simp [QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_mul' x y := by ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  map_add' x y := by ext <;> simp

private lemma scalar_integral (m d : ℕ) :
    (∀ z : FibAlg (ZMod m), (z^d).im=0) ↔ ∀ z : FibAlg ℤ, (m:ℤ) ∣ (z^d).im := by
  have eqv (z : FibAlg ℤ) : ((reducePair m z)^d).im=0 ↔ (m:ℤ) ∣ (z^d).im := by
    rw [← map_pow]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd ..
  constructor
  · exact fun h z => (eqv z).mp (h _)
  · rintro h ⟨x,y⟩
    obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨b,rfl⟩ := ZMod.intCast_surjective y
    exact (eqv ⟨a,b⟩).mpr (h _)

private lemma principal_pow {R : Type*} [CommRing R] {p : ℕ} (ho : Odd p)
    (b : R) (a : ℕ) :
    ∃ c : R, (1+p*b)^(p^a)=1+(p:R)^(a+1)*(b+p*c) := by
  induction a with
  | zero => exact ⟨0,by simp⟩
  | succ a ih =>
    obtain ⟨c,hc⟩ := ih
    let v := (p:R)^a*(b+p*c)
    obtain ⟨w,hw⟩ := odd_sq_dvd_geom_sum₂_sub (1:R) v ho
    simp only [one_pow,mul_one] at hw
    have hg := geom_sum₂_mul (1+p*v) (1:R) p
    simp only [one_pow,mul_one,add_sub_cancel_left] at hg
    have he : (1+(p:R)*v)^p=1+(p+p^2*w)*(p*v) := by
      linear_combination -hg + ((p:R)*v)*hw
    refine ⟨c+(b+p*c)*w,?_⟩
    rw [pow_succ p a,pow_mul,hc,show (p:R)^(a+1)*(b+p*c)=p*v by dsimp [v]; ring,he]
    dsimp [v]
    ring

private lemma principal_first_order {R : Type*} [CommRing R] (p a : ℕ) (b c : R) (l : ℕ) :
    ∃ w : R, (1+(p:R)^(a+1)*(b+p*c))^l =
      1+(p:R)^(a+1)*(l*b+p*w) := by
  obtain ⟨w,hw⟩ := sq_dvd_add_pow_sub_sub ((p:R)^(a+1)*(b+p*c)) 1 l
  simp only [one_pow,one_mul] at hw
  exact ⟨l*c+(p:R)^a*(b+p*c)^2*w,by linear_combination hw⟩

private lemma principal_order {p d k : ℕ} (hp : p.Prime) (ho : Odd p) (hd : 0<d)
    (b : FibAlg ℤ) (hb : ¬(p:ℤ) ∣ b.im)
    (hz : (p:ℤ)^(k+1) ∣ ((1+(p:FibAlg ℤ)*b)^d).im) : p^k ∣ d := by
  obtain ⟨a,l,hl,rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p hp.ne_one
  by_cases h : k≤a
  · exact (pow_dvd_pow p h).trans (dvd_mul_right ..)
  obtain ⟨c,hc⟩ := principal_pow ho b a
  obtain ⟨w,hw⟩ := principal_first_order p a b c l
  rw [pow_mul,hc,hw] at hz
  have he (u v : ℕ) (z : FibAlg ℤ) : (((u:FibAlg ℤ)^v)*z).im=(u:ℤ)^v*z.im := by
    simp only [← Nat.cast_pow,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,
      QuadraticAlgebra.im_natCast,zero_mul,mul_zero,add_zero]
  simp only [QuadraticAlgebra.im_add,QuadraticAlgebra.im_one,zero_add,he] at hz
  have hdiv : (p:ℤ)^(a+1)*p ∣ (p:ℤ)^(a+1)*(((l:FibAlg ℤ)*b).im+((p:FibAlg ℤ)*w).im) :=
    (show (p:ℤ)^(a+1)*p ∣ (p:ℤ)^(k+1) by rw [←pow_succ]; exact pow_dvd_pow _ (by omega)).trans hz
  have h' := Int.dvd_of_mul_dvd_mul_left (pow_ne_zero (a+1) (by exact_mod_cast hp.ne_zero)) hdiv
  simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,QuadraticAlgebra.im_natCast,
    zero_mul,mul_zero,add_zero] at h'
  have base := (Int.dvd_add_left (dvd_mul_right (p:ℤ) w.im)).mp h'
  exact False.elim (((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd base).elim
    (fun e => hl (by exact_mod_cast e)) hb)


private lemma integer_im_mul (t : ℤ) (z : FibAlg ℤ) :
    ((t:FibAlg ℤ)*z).im=t*z.im := by
  simp [QuadraticAlgebra.im_mul,QuadraticAlgebra.re_intCast,QuadraticAlgebra.im_intCast]

private lemma scalar_lift_step (p a : ℕ) (z : FibAlg ℤ) (h : (p:ℤ)^(a+1) ∣ z.im) :
    (p:ℤ)^(a+2) ∣ (z^p).im := by
  obtain ⟨v,hv⟩ := h
  let b : FibAlg ℤ := ⟨0,v⟩
  let A := (p:ℤ)^(a+1)
  have he : z=(z.re:FibAlg ℤ)+(A:FibAlg ℤ)*b := by
    ext <;> simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul,QuadraticAlgebra.re_intCast,QuadraticAlgebra.im_intCast,b,
      mul_zero,zero_mul,add_zero,zero_add]
    · rfl
    · exact hv
  obtain ⟨w,hw⟩ := sq_dvd_add_pow_sub_sub ((A:FibAlg ℤ)*b) (z.re:FibAlg ℤ) p
  rw [←he] at hw
  have hpow : z^p=(((z.re^(p-1)*A*(p:ℤ):ℤ):FibAlg ℤ)*b)+
      (z.re^p:ℤ)+(A^2:ℤ)*(b^2*w) := by
    push_cast
    linear_combination hw
  rw [hpow]
  simp only [QuadraticAlgebra.im_add,integer_im_mul,QuadraticAlgebra.im_intCast,add_zero]
  exact ⟨z.re^(p-1)*b.im+(p:ℤ)^a*(b^2*w).im,by dsimp [A]; ring⟩

private lemma scalar_lift (p k d : ℕ)
    (h : ∀ z : FibAlg ℤ, (p:ℤ) ∣ (z^d).im) :
    ∀ z : FibAlg ℤ, (p:ℤ)^(k+1) ∣ (z^(d*p^k)).im := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro z
    rw [pow_succ p k,←Nat.mul_assoc,pow_mul]
    exact scalar_lift_step p k _ (ih z)

private lemma scalar_five_suff (z : FibAlg ℤ) (k : ℕ) : (5:ℤ)^k ∣ (z^(5^k)).im := by
  induction k with
  | zero => simp
  | succ k ih =>
    have five (w : FibAlg ℤ) : 5*w.im ∣ (w^5).im := by
      obtain ⟨u,v⟩ := w
      exact ⟨u^4+2*u^3*v+4*u^2*v^2+3*u*v^3+v^4,by
        simp only [pow_succ,pow_zero,one_mul,QuadraticAlgebra.mk_mul_mk]; ring⟩
    rw [pow_succ (5:ℕ),pow_mul,pow_succ (5:ℤ),mul_comm]
    exact (mul_dvd_mul_left 5 ih).trans (five _)

private lemma scalar_five_necessary {d k : ℕ} (hd : 0<d)
    (h : ∀ z : FibAlg ℤ, (5:ℤ)^(k+1) ∣ (z^d).im) : 5^(k+1) ∣ d := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let z : FibAlg ℤ := ⟨0,2⟩
  let w : FibAlg (ZMod 5) := ⟨-1,2⟩
  have zero : w*w=0 := by decide
  have tangent (n : ℕ) : (1+w)^n=1+n*w := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih,Nat.cast_succ]
      linear_combination n*zero
  have base : 5 ∣ d := by
    have he := ((scalar_integral 5 d).mpr (fun t =>
      (dvd_pow_self (5:ℤ) (Nat.succ_ne_zero k)).trans (h t))) (1+w)
    rw [tangent] at he
    change (0:ZMod 5)+((d:ZMod 5)*2+0*(-1)+1*0*2)=0 at he
    have hzero : (d:ZMod 5)=0 := (mul_eq_zero.mp (by simpa using he : (d:ZMod 5)*2=0)).resolve_right (by decide)
    exact (ZMod.natCast_eq_zero_iff d 5).mp hzero
  obtain ⟨l,rfl⟩ := base
  let b : FibAlg ℤ := ⟨19,32⟩
  have hz : z^5=1+5*b := by decide
  have hv := h z
  rw [pow_mul,hz] at hv
  have hh := principal_order (p:=5) (k:=k) (d:=l) (by decide) (by decide) (by omega) b
    (by decide) hv
  rw [pow_succ']
  exact mul_dvd_mul_left _ hh


/-- A prime power divides every integral value of the upper index form exactly
when it divides the initial term and the step satisfies the relevant ramified
or inert exponent condition. The exponent is written as `k+1`. -/
theorem upperIndexForm_fixed_prime_power (r d k : ℕ) {p : ℕ} (hp : p.Prime) (hd : 0<d) :
    (∀ x y : ℤ, (p:ℤ)^(k+1) ∣ upperIndexForm x y d r) ↔
    p^(k+1) ∣ lucasFibonacciSum r ∧
      ((p=5 ∧ p^(k+1) ∣ d) ∨ ((p%5=2 ∨ p%5=3) ∧ (p+1)*p^k ∣ d)) := by
  rw [←Nat.cast_pow,fixed_iff_scalar,scalar_integral]
  push_cast
  constructor
  · rintro ⟨hu,h⟩
    refine ⟨hu,?_⟩
    by_cases h5 : p=5
    · subst p
      exact Or.inl ⟨rfl,scalar_five_necessary hd h⟩
    have h₁ := (scalar_integral p d).mpr (fun z =>
      (dvd_pow_self (p:ℤ) (Nat.succ_ne_zero k)).trans (h z))
    have hi : ∀ a : ZMod p, a^2 ≠ 1+1*a := by
      intro a ha
      exact scalar_powers_split hp h5 hd (by simpa using ha) h₁
    have hbase := (scalar_powers_inert hp hd hi).mp h₁
    have hpk : p^k ∣ d := by
      by_cases h2 : p=2
      · subst p
        have hk : k<2 := by
          by_contra! hbig
          exact eight_excluded_three_unbounded.1 r ((show 8 ∣ 2^(k+1) from
            pow_dvd_pow 2 (show 3≤k+1 by omega)).trans hu)
        interval_cases k
        · simp
        · let b : FibAlg ℤ := ⟨0,1⟩
          obtain ⟨w,hw⟩ := principal_first_order 2 0 b 0 d
          norm_num at hw
          have hz := h (1+2*b)
          rw [hw] at hz
          have he : (4:ℤ) ∣ 2*((d:ℤ)+2*w.im) := by
            simpa [QuadraticAlgebra.im_one,QuadraticAlgebra.re_natCast,QuadraticAlgebra.im_natCast,
              show (2:FibAlg ℤ).re=2 from rfl,show (2:FibAlg ℤ).im=0 from rfl,b] using hz
          have hh : (2:ℤ) ∣ (d:ℤ)+2*w.im := Int.dvd_of_mul_dvd_mul_left (by decide : (2:ℤ) ≠ 0) he
          simpa using (show 2 ∣ d by exact_mod_cast (Int.dvd_add_left (dvd_mul_right (2:ℤ) w.im)).mp hh)
      · let b : FibAlg ℤ := ⟨0,1⟩
        have hb : ¬(p:ℤ) ∣ b.im := by
          change ¬(p:ℤ) ∣ 1
          exact_mod_cast (Nat.dvd_one.mp.mt hp.ne_one)
        exact principal_order hp (hp.odd_of_ne_two h2) hd b hb (h _)
    have cop : (p+1).Coprime (p^k) := (show (p+1).Coprime p by simp).pow_right k
    exact Or.inr ⟨(fibonacci_nonsplit_mod_five hp h5).mp hi,cop.mul_dvd_of_dvd_of_dvd hbase hpk⟩
  · rintro ⟨hu,hdv⟩
    refine ⟨hu,fun z => ?_⟩
    rcases hdv with ⟨rfl,e,rfl⟩ | ⟨hres,e,rfl⟩
    · rw [Nat.mul_comm,pow_mul]
      exact scalar_five_suff _ _
    · have h5 : p≠5 := by rintro rfl; norm_num at hres
      have hi := (fibonacci_nonsplit_mod_five hp h5).mpr hres
      have hs := (scalar_integral p (p+1)).mp
        ((scalar_powers_inert hp (Nat.succ_pos _) hi).mpr dvd_rfl)
      rw [Nat.mul_comm ((p+1)*p^k) e,pow_mul]
      exact scalar_lift p k (p+1) hs _


private lemma form_scale {R : Type*} [CommRing R] (u x y : R) (r d : ℕ) :
    upperIndexForm (u*x) (u*y) d r=u^d*upperIndexForm x y d r := by
  induction d generalizing r with
  | zero => simp [upperIndexForm]
  | succ d ih => simp only [upperIndexForm,ih,pow_succ]; ring

/-- Over a residue ring, the two points zero and one force
the leading coefficient to vanish and the Fibonacci step to be scalar. -/
private lemma affine_points {m r d : ℕ}
    (h : ∀ x : ZMod m, upperIndexForm x 1 d r=0) :
    (lucasFibonacciSum r:ZMod m)=0 ∧
    ((⟨0,1⟩:FibAlg (ZMod m))^d).im=0 ∧ IsUnit (((⟨0,1⟩:FibAlg (ZMod m))^d).re) := by
  let R := ZMod m
  let w : FibAlg R := ⟨0,1⟩
  let t := w^d
  let A : R := lucasFibonacciSum r
  let B : R := lucasFibonacciSum (r+1)
  have eq0 : A*t.re+B*t.im=0 := (upperIndexForm_power _ _ _ _).symm.trans (h 0)
  have eq1 : A*(t*t).re+B*(t*t).im=0 := by
    have h' := (upperIndexForm_power _ _ _ _).symm.trans (h 1)
    have hw : (⟨1,1⟩:FibAlg R)=w*w := by ext <;> simp [w]
    simpa only [hw,mul_pow] using h'
  have norm : IsUnit t.norm := by
    have hneg : w.norm=(-1:R) := by simp [w,QuadraticAlgebra.norm_def]
    exact (show w.norm^d=t.norm from (map_pow _ _ _).symm) ▸
      (hneg ▸ (isUnit_one.neg.pow d))
  have hA : A=0 := by
    apply norm.mul_right_eq_zero.mp
    simp only [QuadraticAlgebra.norm_def,one_mul]
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,one_mul] at eq1
    linear_combination (2*t.re+t.im)*eq0-eq1
  have hu := (ZMod.natCast_eq_zero_iff ..).mp hA
  have hB : IsUnit B := (ZMod.isUnit_iff_coprime ..).mpr ((coprime_next r).of_dvd_left hu).symm
  have ht : t.im=0 := hB.mul_right_eq_zero.mp (by simpa [hA] using eq0)
  refine ⟨hA,ht,?_⟩
  rw [QuadraticAlgebra.norm_def,ht] at norm
  simpa using norm

private lemma affine_chart {m r d : ℕ} (h : ∀ x : ZMod m, upperIndexForm x 1 d r=0)
    (x y : ZMod m) (hy : IsUnit y ∨ IsUnit (x+y)) : upperIndexForm x y d r=0 := by
  have chart (a b : ZMod m) (hb : IsUnit b) : upperIndexForm a b d r=0 := by
    obtain ⟨u,rfl⟩ := hb
    have hs := form_scale (u:ZMod m) ((↑u⁻¹:ZMod m)*a) 1 r d
    simpa [←mul_assoc,h] using hs
  rcases hy with hy|hy
  · exact chart x y hy
  · obtain ⟨_,ht,hu⟩ := affine_points h
    let w : FibAlg (ZMod m) := ⟨0,1⟩
    let z : FibAlg (ZMod m) := ⟨x,y⟩
    have prod : (⟨y,x+y⟩:FibAlg (ZMod m))=w*z := by ext <;> simp [w,z]
    have hrot := chart y (x+y) hy
    rw [upperIndexForm_power,prod,mul_pow] at hrot
    apply hu.mul_right_eq_zero.mp
    rw [upperIndexForm_power]
    change (w^d).re*(_*(z^d).re+_*(z^d).im)=0
    change (w^d).im=0 at ht
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,ht,zero_mul,mul_zero,add_zero] at hrot
    linear_combination hrot

private lemma affine_binary (r d e : ℕ) {p : ℕ} (hp : p.Prime) (hd : 0<d)
    (h : ∀ x : ℤ, (p:ℤ)^e ∣ upperIndexForm x 1 d r) :
    ∀ x y : ℤ, (p:ℤ)^e ∣ upperIndexForm x y d r := by
  induction e with
  | zero => simp
  | succ e ih =>
    let m := p^(e+1)
    have h' (x : ZMod m) : upperIndexForm x 1 d r=0 := by
      obtain ⟨n,rfl⟩ := ZMod.intCast_surjective x
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr
        (show (m:ℤ) ∣ upperIndexForm n 1 d r by simpa [m] using h n)
      simpa only [form_cast,Int.cast_one] using hz
    have unit (n : ℤ) (hn : ¬(p:ℤ) ∣ n) : IsUnit (n:ZMod m) := by
      apply (ZMod.coe_int_isUnit_iff_isCoprime ..).mpr
      dsimp [m]
      exact (((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hn).pow_left)
    intro x y
    by_cases hy : (p:ℤ) ∣ y
    · by_cases hx : (p:ℤ) ∣ x
      · obtain ⟨a,rfl⟩ := hx
        obtain ⟨b,rfl⟩ := hy
        rw [form_scale,pow_succ,mul_comm ((p:ℤ)^e)]
        exact mul_dvd_mul (dvd_pow_self _ hd.ne')
          (ih (fun n => (pow_dvd_pow (p:ℤ) (Nat.le_succ e)).trans (h n)) a b)
      · have hxy : ¬(p:ℤ) ∣ x+y := by
          intro hsum
          exact hx ((Int.dvd_add_left hy).mp hsum)
        have hz := affine_chart h' (x:ZMod m) (y:ZMod m)
          (Or.inr (by simpa using unit (x+y) hxy))
        rw [←form_cast] at hz
        simpa [m] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp hz
    · have hz := affine_chart h' (x:ZMod m) (y:ZMod m) (Or.inl (unit y hy))
      rw [←form_cast] at hz
      simpa [m] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp hz

private lemma index_eval (r d : ℕ) (x : ℤ) :
    (upperIndexPolynomial r d).eval x=upperIndexForm x 1 d r := by
  induction d generalizing r with
  | zero => simp [upperIndexPolynomial,upperIndexForm]
  | succ d ih =>
    change (Polynomial.X*upperIndexPolynomial r d+1*upperIndexPolynomial (r+1) d).eval x=_
    simp [upperIndexForm,ih]

/-- The fixed prime powers of the univariate irreducible polynomial are
exactly the fixed prime powers of the binary form. -/
theorem upperIndexPolynomial_fixed_prime_power (r d k : ℕ) {p : ℕ} (hp : p.Prime) (hd : 0<d) :
    (∀ x : ℤ, (p:ℤ)^(k+1) ∣ (upperIndexPolynomial r d).eval x) ↔
    p^(k+1) ∣ lucasFibonacciSum r ∧
      ((p=5 ∧ p^(k+1) ∣ d) ∨ ((p%5=2 ∨ p%5=3) ∧ (p+1)*p^k ∣ d)) := by
  simp_rw [index_eval]
  rw [←upperIndexForm_fixed_prime_power r d k hp hd]
  exact ⟨affine_binary r d (k+1) hp hd,fun h x => h x 1⟩

/-- Primitive irreducible members of the family can have arbitrarily large powers
of three dividing every value at an integer. -/
theorem upper_primitive_forms_unbounded_fixed_powers (k : ℕ) :
    ∃ r d : ℕ, 0<d ∧ (upperIndexPolynomial r d).IsPrimitive ∧
      Irreducible ((upperIndexPolynomial r d).map (Int.castRingHom ℚ)) ∧
      ∀ x : ℤ, (3:ℤ)^(k+2) ∣ (upperIndexPolynomial r d).eval x := by
  obtain ⟨t,_,hu⟩ := eight_excluded_three_unbounded.2 k
  let r := 3+12*t
  let d := 4*3^(k+1)
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨r,d,hd,?_,upperIndexPolynomial_irreducible r d hd,?_⟩
  · intro a ha
    apply Int.isUnit_iff_natAbs_eq.mpr
    by_contra hn
    obtain ⟨p,hp,hpa⟩ := Nat.exists_prime_and_dvd hn
    have hc := (Int.natCast_dvd.mpr hpa).trans (Polynomial.dvd_content_iff_C_dvd.mpr ha)
    have H := (upperIndexPolynomial_prime_power_content r d hd (p:=p) (k:=1) hp
      (by decide)).mp (by simpa using hc)
    obtain ⟨rfl,_,hfive⟩ := H
    have h' : ¬5 ∣ d := by
      dsimp [d]
      exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).not.mpr
        (not_or.mpr ⟨by decide,fun h => (by decide : ¬5 ∣ 3) ((by decide : Nat.Prime 5).dvd_of_dvd_pow h)⟩)
    exact h' (by simpa using hfive)
  · exact (upperIndexPolynomial_fixed_prime_power r d (k+1) (p:=3) (by decide) hd).mpr
      ⟨hu,Or.inr ⟨by decide,dvd_rfl⟩⟩

#print axioms fibonacci_nonsplit_mod_five
#print axioms upperIndexForm_power
#print axioms upperIndexForm_fixed_prime_power
#print axioms upperIndexPolynomial_fixed_prime_power
#print axioms upper_primitive_forms_unbounded_fixed_powers

end Arxiv.«2211.10788»
