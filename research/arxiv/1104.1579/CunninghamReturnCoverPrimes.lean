import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Algebra.Polynomial.Roots

/-! # Covering primes for Cunningham return indices -/

namespace CunninghamChain.ReturnCover
open Polynomial Filter

/-- An odd cyclotomic index survives reduction at a prime divisor of its
value at a negative dyadic power, once that power is sufficiently deep. -/
theorem prime_of_negative_cyclotomic {m a : ℕ} (hm : Odd m) (hm₁ : 1<m)
    (hma : m≤2^a) (hsize : 1<((cyclotomic m ℤ).eval (-(2:ℤ)^(2^a))).natAbs) :
    ∃ q : ℕ, q.Prime ∧ 2^a<q ∧ orderOf (-(2:ZMod q)^(2^a))=m := by
  let z := -(2:ℤ)^(2^a)
  let v := (cyclotomic m ℤ).eval z
  let q := v.natAbs.minFac
  have hq : q.Prime := Nat.minFac_prime (ne_of_gt hsize)
  let : Fact q.Prime := ⟨hq⟩
  have hcast : (v:ZMod q)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
    (Int.dvd_natAbs.mp (by exact_mod_cast Nat.minFac_dvd v.natAbs))
  have hroot : (cyclotomic m (ZMod q)).IsRoot (-(2:ZMod q)^(2^a)) := by
    change ((cyclotomic m (ZMod q)).eval _)=0
    rw [←map_cyclotomic_int m (ZMod q)]
    have heval := Polynomial.eval_map_apply (p:=cyclotomic m ℤ) (Int.castRingHom (ZMod q)) z
    simpa [z] using heval.trans hcast
  obtain he := hroot.dvd (cyclotomic.dvd_X_pow_sub_one m (ZMod q))
  have hz : (-(2:ZMod q)^(2^a))^m=1 := by simpa [IsRoot,sub_eq_zero] using he
  have hdiv : q ∣ (2^m)^(2^a)+1 := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    push_cast
    rw [hm.neg_pow,pow_right_comm] at hz
    linear_combination -hz
  have h2 : q≠2 := by
    intro heq
    rw [heq] at hdiv
    have hpow : 2 ∣ (2^m)^(2^a) :=
      (dvd_pow_self 2 (by omega : m≠0)).trans (dvd_pow_self _ (by positivity : 2^a≠0))
    exact (by decide : ¬ 2 ∣ 1) ((Nat.dvd_add_iff_right hpow).mpr hdiv)
  obtain ⟨k,hk⟩ := Nat.pow_pow_add_primeFactors_one_lt hq h2 hdiv
  have hqt := hq.one_lt
  have hpos : 0<k := by
    cases k with
    | zero => simp at hk; omega
    | succ k => omega
  have hlt : 2^a<q := by
    have hpow := Nat.le_mul_of_pos_left (2^(a+1)) hpos
    rw [pow_succ] at hpow hk
    omega
  have : NeZero (m:ZMod q) := NeZero.of_not_dvd _ (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  exact ⟨q,hq,hlt,(isRoot_cyclotomic_iff.mp hroot).eq_orderOf.symm⟩

/-- Every sufficiently deep dyadic power admits a covering prime with the
prescribed odd order after negation. -/
theorem eventually_prime_of_odd_order {m : ℕ} (hm : Odd m) (hm₁ : 1<m) :
    ∀ᶠ a : ℕ in atTop, ∃ q : ℕ, q.Prime ∧ 2^a<q ∧ orderOf (-(2:ZMod q)^(2^a))=m := by
  let z (a : ℕ) := -(2:ℤ)^(2^a)
  have hz : Function.Injective z := by
    intro a b h
    have hp : (2:ℤ)^(2^a)=(2:ℤ)^(2^b) := neg_injective h
    exact (Nat.pow_right_injective (by decide : 2≤2)) ((pow_right_strictMono₀ (by decide : (1:ℤ)<2)).injective hp)
  have hf := (cyclotomic m ℤ).tendstoCofinite_of_natDegree_ne_zero (by
    rw [natDegree_cyclotomic]; exact (Nat.totient_pos.mpr (by omega)).ne')
  have ht : Tendsto (fun a => (cyclotomic m ℤ).eval (z a)) atTop cofinite :=
    hf.1.comp (Nat.cofinite_eq_atTop ▸ hz.tendsto_cofinite)
  have he := ht.eventually ((Set.finite_Icc (-1:ℤ) 1).compl_mem_cofinite)
  filter_upwards [he,eventually_ge_atTop m] with a ha hma
  apply prime_of_negative_cyclotomic hm hm₁ (hma.trans ((Nat.lt_two_pow_self (n:=a)).le))
  change (cyclotomic m ℤ).eval (z a) ∉ Set.Icc (-1:ℤ) 1 at ha
  simp only [Set.mem_Icc,not_and_or,not_le] at ha
  change 1 < ((cyclotomic m ℤ).eval (z a)).natAbs
  omega

private theorem later_dyadic_order {q a b m : ℕ} (hm : Odd m) (hab : a<b)
    (h : orderOf (-(2:ZMod q)^(2^a))=m) : orderOf ((2:ZMod q)^(2^b))=m := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hab)
  let x := -(2:ZMod q)^(2^a)
  have hpow : (2:ZMod q)^(2^(a+1+j))=x^(2*2^j) := by
    rw [pow_add,pow_succ,pow_mul,pow_mul,pow_mul]
    simp [x]
  rw [hpow]
  have hc : (orderOf x).Coprime (2*2^j) := by
    rw [show orderOf x=m from h]
    exact (Nat.coprime_two_right.mpr hm).mul_right ((Nat.coprime_two_right.mpr hm).pow_right _)
  exact hc.orderOf_pow.trans h

private theorem distinct_dyadic_depths {q a b m : ℕ} (hq : q.Prime) (hq₂ : 2<q)
    (hm : Odd m) (hab : a<b) (ha : orderOf (-(2:ZMod q)^(2^a))=m)
    (hb : orderOf (-(2:ZMod q)^(2^b))=m) : False := by
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (2<q) := ⟨hq₂⟩
  have hp := later_dyadic_order hm hab ha
  have hp' : ((2:ZMod q)^(2^b))^m=1 := by rw [←hp,pow_orderOf_eq_one]
  have hn : (-(2:ZMod q)^(2^b))^m=1 := by rw [←hb,pow_orderOf_eq_one]
  rw [hm.neg_pow,hp'] at hn
  exact ZMod.neg_one_ne_one hn

/-- At a common dyadic exponent the base has any prescribed odd order at
arbitrarily many distinct odd primes. The common exponent can be taken above a cutoff. -/
theorem simultaneous_order_primes {m : ℕ} (hm : Odd m) (hm₁ : 1<m) (L n : ℕ) :
    ∃ B : ℕ, L≤B ∧ ∃ q : ℕ → ℕ, (∀ i<n, (q i).Prime ∧ 2<q i ∧
      orderOf ((2:ZMod (q i))^(2^B))=m) ∧ Set.InjOn q (Set.Iio n) := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_prime_of_odd_order hm hm₁)
  let e (i : ℕ) := A+L+2+i
  have haux (i : ℕ) := hA (e i) (by dsimp [e]; omega)
  choose q hq using haux
  have hgt (i : ℕ) : 2<q i := by
    have h := Nat.lt_two_pow_self (n:=e i)
    have := (hq i).2.1
    dsimp [e] at *
    omega
  refine ⟨e n,by dsimp [e]; omega,q,fun i hi => ⟨(hq i).1,hgt i,?_⟩,?_⟩
  · exact later_dyadic_order hm (by dsimp [e]; omega) (hq i).2.2
  · have f {i j : ℕ} (hlt : i<j) (he : q i=q j) : False := by
      have h := (hq i).2.2
      rw [he] at h
      exact distinct_dyadic_depths (hq j).1 (hgt j) hm (by dsimp [e]; omega) h (hq j).2.2
    intro i _ j _ he
    rcases lt_trichotomy i j with h|h|h
    · exact (f h he).elim
    · exact h
    · exact (f h he.symm).elim

/-- After the forbidden dyadic depth, every later dyadic power is one. -/
theorem fermat_power_later {q a B : ℕ} (ha : a<B)
    (hf : (2:ZMod q)^(2^a) = -1) : (2:ZMod q)^(2^B)=1 := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ha)
  rw [pow_add,pow_succ,pow_mul,pow_mul,hf,neg_one_sq,one_pow]

/-- The Fermat numbers give one odd prime for each dyadic valuation.
A power of two misses all the first B forbidden residues exactly at the
indices divisible by 2^B. -/
theorem fermat_cover : ∃ q : ℕ → ℕ, Function.Injective q ∧
    (∀ i, (q i).Prime ∧ 2<q i ∧ (2:ZMod (q i))^(2^i) = -1) ∧
    ∀ B j : ℕ, (∀ i<B, (2:ZMod (q i))^j ≠ -1) ↔ 2^B ∣ j := by
  let q (i : ℕ) := (Nat.fermatNumber i).minFac
  have gt (i : ℕ) : 1<Nat.fermatNumber i := by simp [Nat.fermatNumber]
  have pr (i : ℕ) : (q i).Prime := Nat.minFac_prime (gt i).ne'
  have dv (i : ℕ) : q i ∣ Nat.fermatNumber i := Nat.minFac_dvd _
  have qt (i : ℕ) : 2<q i := by
    have hh := (pr i).two_le
    have h := Nat.odd_fermatNumber i
    by_contra! hbad
    have heq : q i=2 := by omega
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr (heq ▸ dv i))
  have hp (i : ℕ) : (2:ZMod (q i))^(2^i) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [Nat.fermatNumber,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff ..).mpr (dv i)
  refine ⟨q,?_,fun i => ⟨pr i,qt i,hp i⟩,?_⟩
  · intro i j he
    by_contra h
    have hcop := Nat.coprime_fermatNumber_fermatNumber h
    exact (pr i).not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dv i) (he ▸ dv j))
  · intro B j
    constructor
    · intro hn
      by_contra hnd
      have hj : j≠0 := by rintro rfl; exact hnd (dvd_zero _)
      obtain ⟨a,u,hu,hju⟩ := Nat.exists_eq_two_pow_mul_odd hj
      have ha : a<B := by
        by_contra! h
        exact hnd (hju ▸ (pow_dvd_pow 2 h).trans (dvd_mul_right _ _))
      apply hn a ha
      rw [hju,pow_mul,hp,hu.neg_pow,one_pow]
    · rintro ⟨u,rfl⟩ i hi
      let : Fact (2<q i) := ⟨qt i⟩
      rw [pow_mul,fermat_power_later hi (hp i),one_pow]
      exact ZMod.neg_one_ne_one.symm

#print axioms fermat_power_later
#print axioms fermat_cover

#print axioms simultaneous_order_primes

#print axioms eventually_prime_of_odd_order

#print axioms prime_of_negative_cyclotomic

end CunninghamChain.ReturnCover
