import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciAffineGCD
import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes

/-! Prime divisors on the upper Hosoya diagonal at prime parameters. -/

namespace Arxiv.«2211.10788»

/-- Two applications of Frobenius fix either golden-ratio root. -/
private lemma golden_frobenius_twice {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharP K q]
    {a : K} (ha : a*a=a+1) : a^(q*q)=a := by
  let F := frobenius K q
  have hF : F a*F a = F a+1 := by simpa [map_mul,map_add] using congrArg F ha
  have hfac : (F a-a)*(F a-(1-a))=0 := by linear_combination hF-ha
  have h := mul_eq_zero.mp hfac
  have hfix : F (F a)=a := by
    rcases h with h|h
    · rw [sub_eq_zero.mp h,sub_eq_zero.mp h]
    · have h' := sub_eq_zero.mp h
      rw [h',map_sub,map_one,h']
      ring
  simpa [F,frobenius_def,pow_mul] using hfix

private lemma scaled_binet {K : Type*} [Field K] {a b : K} (ha : a*a=a+1) (hb : b*b=b+1)
    (n : ℕ) :
    (a-b)*(lucasFibonacciSum n:K)=(4-b)*a^n-(4-a)*b^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucas_fibonacci_sum_zero]
  | one => simp [lucas_fibonacci_sum_one]; ring
  | more n h₀ h₁ =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,mul_add,h₁,h₀]
    rw [pow_add a n 2,pow_add b n 2,pow_two,pow_two,ha,hb,pow_succ,pow_succ]
    ring


/-- Modulo every prime greater than five the upper sequence has q²−1 as a period. -/
theorem upper_quadratic_field_period {q : ℕ} (hq : q.Prime) (hl : 5 < q) (n : ℕ) :
    lucasFibonacciSum (n+(q*q-1)) ≡ lucasFibonacciSum n [MOD q] := by
  let : Fact q.Prime := ⟨hq⟩
  let K := AlgebraicClosure (ZMod q)
  open Polynomial in
    obtain ⟨a,ha⟩ := IsAlgClosed.exists_root (X^2-X-1 : K[X])
      (by have h : (X^2-X-1 : K[X]).degree=2 := by compute_degree!
          rw [h]; decide)
  have hh : a*a=a+1 := by
    simp only [Polynomial.IsRoot,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] at ha
    linear_combination ha
  let b := 1-a
  have hb : b*b=b+1 := by dsimp [b]; linear_combination hh
  have hab : a-b ≠ 0 := by
    have h : (a-b)^2=5 := by dsimp [b]; linear_combination 4*hh
    intro he
    rw [he,zero_pow (by decide)] at h
    have h5 : (5:K)≠0 := by exact_mod_cast (CharP.cast_eq_zero_iff K q 5).not.mpr (by intro hd; have := Nat.le_of_dvd (by decide : 0<5) hd; omega)
    exact h5 h.symm
  have fix (z : K) (hz : z*z=z+1) : z^(q*q-1)=1 := by
    have hz0 : z≠0 := by rintro rfl; simp at hz
    apply mul_right_cancel₀ hz0
    rw [one_mul,←pow_succ,show q*q-1+1=q*q by have := Nat.mul_pos hq.pos hq.pos; omega]
    exact golden_frobenius_twice hz
  have hbig := scaled_binet hh hb (n+(q*q-1))
  rw [pow_add,pow_add,fix a hh,fix b hb,mul_one,mul_one] at hbig
  have h := mul_left_cancel₀ hab (hbig.trans (scaled_binet hh hb n).symm)
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  apply (algebraMap (ZMod q) K).injective
  simpa only [map_natCast] using h


/-- At primes congruent to −1 modulo five, Frobenius fixes both roots, so
evaluating the index form at the prime agrees with evaluation at one. -/
theorem upper_split_prime_parameter {p : ℕ} (hp : p.Prime) (hl : 5 < p) (h5 : p % 5 = 4)
    (r d : ℕ) : lucasFibonacciSum (r+d*p) ≡ lucasFibonacciSum (r+d) [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h4 : (p : ZMod 5)=4 := by
    exact (ZMod.natCast_eq_natCast_iff p 4 5).mpr h5
  have hs : IsSquare (5:ZMod p) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=5) (q:=p) (by decide) (by omega)).mp
      (h4 ▸ (show IsSquare (4:ZMod 5) from ⟨2,by decide⟩))
  obtain ⟨z,hz⟩ := hs
  have htwo : (2:ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr (by intro h; have := Nat.le_of_dvd (by decide : 0<2) h; omega)
  have hfive : (5:ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 5 p).not.mpr (by intro h; have := Nat.le_of_dvd (by decide : 0<5) h; omega)
  let a := (1+z)/2
  let b := (1-z)/2
  have ha : a*a=a+1 := by dsimp [a]; field_simp; linear_combination -hz
  have hb : b*b=b+1 := by dsimp [b]; field_simp; linear_combination -hz
  have hab : a-b ≠ 0 := by
    have h : a-b=z := by dsimp [a,b]; field_simp; ring
    rw [h]
    intro h0
    exact hfive (by simpa [h0] using hz)
  have rootpow (v : ZMod p) : v^(r+d*p)=v^(r+d) := by
    rw [pow_add,Nat.mul_comm d p,pow_mul,ZMod.pow_card,pow_add]
  have h := scaled_binet ha hb (r+d*p)
  rw [rootpow,rootpow] at h
  exact (ZMod.natCast_eq_natCast_iff ..).mp (mul_left_cancel₀ hab (h.trans (scaled_binet ha hb _).symm))

private def upperInt (z : ℤ) : ℤ := 3 * Int.fib z + Int.fib (z+1)

private lemma upperInt_nat (n : ℕ) : upperInt (n:ℤ) = (lucasFibonacciSum n:ℤ) := by
  unfold upperInt lucasFibonacciSum
  rw [←Nat.cast_add_one,Int.fib_natCast,Int.fib_natCast,Nat.fib_add_two]
  push_cast
  ring

private lemma upperInt_step (z : ℤ) : upperInt (z+2)=upperInt z+upperInt (z+1) := by
  unfold upperInt
  have h := Int.fib_add_two (z+1)
  rw [show z+2+1=z+1+2 by ring,h,show z+1+1=z+2 by ring,Int.fib_add_two z]
  ring

private lemma upper_strict : StrictMono lucasFibonacciSum := by
  intro a b h
  exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono h.le)) (Nat.fib_add_two_strictMono h)

private lemma negative_upper (k : ℕ) :
    (upperInt (-((k+1:ℕ):ℤ))).natAbs = 3*Nat.fib (k+1)-Nat.fib k := by
  have hle := Nat.fib_le_fib_succ (n:=k)
  have he : upperInt (-((k+1:ℕ):ℤ)) = (-1:ℤ)^k * (3*(Nat.fib (k+1):ℤ)-Nat.fib k) := by
    unfold upperInt
    rw [show -((k+1:ℕ):ℤ)+1=-(k:ℤ) by push_cast; ring,Int.fib_neg_natCast,Int.fib_neg_natCast]
    ring
  rw [he,Int.natAbs_mul,Int.natAbs_pow]
  simp only [Int.natAbs_neg,Int.natAbs_one,one_pow,one_mul]
  omega

private lemma anchor_bounds (r d : ℕ) (hd : 0 < d) :
    0 < (upperInt ((r:ℤ)-d)).natAbs ∧
      (upperInt ((r:ℤ)-d)).natAbs < lucasFibonacciSum (r+d) := by
  by_cases h : d ≤ r
  · rw [←Nat.cast_sub h,upperInt_nat,Int.natAbs_natCast]
    have hz := upper_strict.monotone (Nat.zero_le (r-d))
    rw [lucas_fibonacci_sum_zero] at hz
    exact ⟨hz,upper_strict (by omega)⟩
  · let k := d-r-1
    have he : (r:ℤ)-d = -((k+1:ℕ):ℤ) := by dsimp [k]; omega
    rw [he,negative_upper]
    have hf := Nat.fib_pos.mpr (by omega : 0<k+1)
    have hle := Nat.fib_le_fib_succ (n:=k)
    have h' := Nat.fib_pos.mpr (by omega : 0<k+1+1)
    have hi : k+1 ≤ r+d := by dsimp [k]; omega
    refine ⟨by omega,lt_of_lt_of_le ?_ (upper_strict.monotone hi)⟩
    simp only [lucasFibonacciSum,Nat.fib_add_two (n:=k+1)]
    omega

private lemma anchor_period (M : ℕ) [NeZero M] (z : ℤ) :
    ∃ T > 0, ∀ n : ℕ, T ∣ n → (upperInt (z+n) : ZMod M) = (upperInt z : ZMod M) := by
  let state (n : ℕ) : ZMod M × ZMod M := (upperInt (z+n), upperInt (z+n+1))
  let step (v : ZMod M × ZMod M) := (v.2,v.1+v.2)
  have hinj : Function.Injective step := by
    rintro ⟨a,b⟩ ⟨c,e⟩ he
    obtain ⟨rfl,h⟩ := Prod.mk.inj (show (b,a+b)=(e,c+e) from he)
    exact Prod.ext (add_right_cancel h) rfl
  have hs : Function.Semiconj state Nat.succ step := by
    intro n
    apply Prod.ext
    · simp [state,step,Nat.cast_succ,add_assoc]
    · simp [state,step,Nat.cast_succ,←add_assoc,show ∀ x : ℤ, x+1+1=x+2 by intro x; ring,upperInt_step]
  obtain ⟨T,hT,hfix⟩ := hinj.mem_periodicPts (state 0)
  refine ⟨T,hT,?_⟩
  rintro _ ⟨k,rfl⟩
  have he := (hs.iterate_right (T*k) 0).trans (hfix.mul_const k).eq
  rw [Nat.succ_iterate] at he
  simpa [state] using congrArg Prod.fst he

private lemma square_one_of_prime_divisors (p C : ℕ) (hC : C ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ C → (q:ZMod p)^2=1) : (C:ZMod p)^2=1 := by
  induction C using induction_on_primes with
  | zero => contradiction
  | one => simp
  | prime_mul q a hq ih =>
    have ha := ih (right_ne_zero_of_mul hC) (fun s hs hd => h s hs (hd.trans (dvd_mul_left ..)))
    rw [Nat.cast_mul,mul_pow,h q hq (dvd_mul_right ..),ha,one_mul]

private lemma prime_factor_for_return {B p u v : ℕ} {w : ℤ} (hw : 0<w.natAbs)
    (hv : w.natAbs<v) (hu : 0<u) (hp : v^2<p)
    (hanchor : (u:ℤ) ≡ w [ZMOD (↑(w.natAbs*B.factorial) : ℤ)])
    (hsplit : u ≡ v [MOD p]) :
    ∃ q > B, q.Prime ∧ q ∣ u ∧ ¬p ∣ q*q-1 := by
  let A := w.natAbs
  have transfer (t : ℕ) (ht : t ∣ A*B.factorial) : t ∣ u ↔ t ∣ A := by
    have ht' : (t:ℤ) ∣ (↑(A*B.factorial):ℤ) := by exact_mod_cast ht
    exact Int.natCast_dvd_natCast.symm.trans ((hanchor.of_dvd ht').dvd_iff.trans Int.natCast_dvd)
  obtain ⟨C,hC⟩ := (transfer A (dvd_mul_right ..)).mpr dvd_rfl
  have big (q : ℕ) (hq : q.Prime) (hd : q ∣ C) : B<q := by
    by_contra! small
    have hA := (transfer (A*q) (Nat.mul_dvd_mul_left A (Nat.dvd_factorial hq.pos small))).mp
      (hC ▸ Nat.mul_dvd_mul_left A hd)
    have hh := Nat.le_of_dvd hw hA
    change A*q ≤ A at hh
    have ha : 0<A := hw
    nlinarith [Nat.mul_le_mul_left A hq.two_le]
  by_contra! none
  have hc0 : C≠0 := by rintro rfl; simp [hC] at hu
  have hc2 := square_one_of_prime_divisors p C hc0 (by
    intro q hq hd
    have h := none q (big q hq hd) hq (hC ▸ hd.trans (dvd_mul_left ..))
    have he := (Nat.modEq_iff_dvd' (by nlinarith [hq.two_le] : 1 ≤ q*q)).mpr h
    simpa [pow_two] using ((ZMod.natCast_eq_natCast_iff 1 (q*q) p).mpr he).symm)
  have H : (v:ZMod p)^2=(A:ZMod p)^2 := by
    rw [←(ZMod.natCast_eq_natCast_iff ..).mpr hsplit,hC,Nat.cast_mul,mul_pow,hc2,mul_one]
  have h := (ZMod.natCast_eq_natCast_iff (v^2) (A^2) p).mp (by simpa using H)
  have small : A^2<v^2 := Nat.pow_lt_pow_left hv (by decide)
  exact small.ne' (h.eq_of_lt_of_lt hp (small.trans hp))

private lemma prime_schedule (r d B : ℕ) (hd : 0<d) :
    ∃ T > 0, ∀ p : ℕ, p.Prime → 5 < p → (lucasFibonacciSum (r+d))^2 < p →
      T ∣ p+1 → ∃ q > B, q.Prime ∧ q ∣ lucasFibonacciSum (r+d*p) ∧ ¬p ∣ q*q-1 := by
  let z : ℤ := (r:ℤ)-d
  let M := (upperInt z).natAbs*B.factorial
  obtain ⟨ha,hv⟩ := anchor_bounds r d hd
  have hm : 0 < M := Nat.mul_pos ha (Nat.factorial_pos _)
  let : NeZero M := ⟨hm.ne'⟩
  obtain ⟨T,hT,period⟩ := anchor_period M z
  refine ⟨5*T,by positivity,?_⟩
  intro p hp hl hcut hdiv
  have hd5 := (show 5 ∣ 5*T from dvd_mul_right ..).trans hdiv
  have h5 : p%5=4 := by omega
  have ht := (show T ∣ 5*T from dvd_mul_left ..).trans hdiv
  have ret := period (d*(p+1)) (ht.trans (dvd_mul_left ..))
  have e : z+(↑(d*(p+1)):ℤ) = (↑(r+d*p):ℤ) := by dsimp [z]; ring
  rw [e,upperInt_nat] at ret
  apply prime_factor_for_return ha hv _ hcut _ (upper_split_prime_parameter hp hl h5 r d)
  · have h := upper_strict.monotone (Nat.zero_le (r+d*p))
    rwa [lucas_fibonacci_sum_zero] at h
  · exact (ZMod.intCast_eq_intCast_iff ..).mp ret


private lemma prime_minus_one (L K : ℕ) (hL : 0 < L) :
    ∃ p > K, p.Prime ∧ L ∣ p+1 := by
  have hc : (L-1).Coprime L := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
    simp
  obtain ⟨p,hp,hpr,he⟩ := Nat.forall_exists_prime_gt_and_modEq K hL.ne' hc
  refine ⟨p,hp,hpr,Nat.modEq_zero_iff_dvd.mp ?_⟩
  have h := he.add_right 1
  rw [show L-1+1=L by omega] at h
  exact h.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)

private lemma repeat_at_parameter {q r d p t : ℕ} (hq : q.Prime) (hlarge : 5<q)
    (hhit : q ∣ lucasFibonacciSum (r+d*p)) (hle : p ≤ t)
    (he : t ≡ p [MOD q*q-1]) : q ∣ lucasFibonacciSum (r+d*t) := by
  have iter (n k : ℕ) :
      lucasFibonacciSum (n+(q*q-1)*k) ≡ lucasFibonacciSum n [MOD q] := by
    induction k with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ k ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (upper_quadratic_field_period hq hlarge _).trans ih
  obtain ⟨k,rfl⟩ := (Nat.modEq_iff_exists_eq_add hle).mp he.symm
  rw [show r+d*(p+(q*q-1)*k)=r+d*p+(q*q-1)*(d*k) by ring]
  exact Nat.modEq_zero_iff_dvd.mp ((iter _ _).trans (Nat.modEq_zero_iff_dvd.mpr hhit))

/-- Distinct nonconstant affine index forms have simultaneous composite values throughout
a reduced residue class of sufficiently large parameters, with distinct prime divisors
above any prescribed bound. -/
theorem simultaneous_prime_parameter_divisors {k : ℕ} (r d : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (hdist : Function.Injective fun i => (r i,d i)) (B : ℕ) :
    ∃ q : Fin k → ℕ, Function.Injective q ∧ (∀ i, B < q i ∧ (q i).Prime) ∧
      ∃ a L N : ℕ, 0 < L ∧ a.Coprime L ∧
        ∀ t : ℕ, N < t → t ≡ a [MOD L] → ∀ i,
          q i ∣ lucasFibonacciSum (r i+d i*t) ∧ ¬(lucasFibonacciSum (r i+d i*t)).Prime := by
  classical
  have sep (i j : Fin k) : ∃ M > 0, i ≠ j → ∀ t,
      (lucasFibonacciSum (r i+d i*t)).gcd (lucasFibonacciSum (r j+d j*t)) ∣ M := by
    by_cases hij : i=j
    · exact ⟨1,by decide,fun h => (h hij).elim⟩
    obtain ⟨M,hM,h⟩ := affine_upper_gcd_bound _ _ _ _ (fun he => hij (hdist he))
    exact ⟨M,hM,fun _ => h⟩
  choose D hD hsep using sep
  let W := max (max B 5) (Finset.univ.sup fun i => Finset.univ.sup (D i))
  choose T hT hs using fun i => prime_schedule (r i) (d i) W (hd i)
  let S := ∏ i, T i
  have hS : 0 < S := Finset.prod_pos fun i _ => hT i
  let K := max 5 (Finset.univ.sup fun i => (lucasFibonacciSum (r i+d i))^2)
  obtain ⟨p,hp,hpr,hret⟩ := prime_minus_one S K hS
  have h5 : 5<p := lt_of_le_of_lt (le_max_left ..) hp
  have one (i : Fin k) := hs i p hpr h5
    ((Finset.le_sup (Finset.mem_univ i)).trans_lt ((le_max_right ..).trans_lt hp))
    ((Finset.dvd_prod_of_mem T (Finset.mem_univ i)).trans hret)
  choose q hq hprime hh havoid using one
  have hq5 (i) : 5 < q i := ((le_max_right B 5).trans (le_max_left ..)).trans_lt (hq i)
  refine ⟨q,?_,fun i => ⟨((le_max_left B 5).trans (le_max_left ..)).trans_lt (hq i),hprime i⟩,?_⟩
  · intro i j he
    by_contra hij
    have hboth := Nat.dvd_gcd (hh i) (he ▸ hh j)
    have hle := Nat.le_of_dvd (hD i j) (hboth.trans (hsep i j hij p))
    have : D i j ≤ W := (Finset.le_sup (f := D i) (Finset.mem_univ j)).trans
      ((Finset.le_sup (f := fun a => Finset.univ.sup (D a)) (Finset.mem_univ i)).trans (le_max_right ..))
    exact (hq i).not_ge (hle.trans this)
  · let L := ∏ i, (q i*q i-1)
    have hL : 0 < L := Finset.prod_pos fun i _ => by nlinarith [hq5 i, Nat.sub_add_cancel (show 1 ≤ q i*q i by nlinarith [hq5 i])]
    have hc : p.Coprime L := Nat.coprime_prod_right_iff.mpr fun i _ => hpr.coprime_iff_not_dvd.mpr (havoid i)
    refine ⟨p,L,max p (Finset.univ.sup q),hL,hc,?_⟩
    intro t ht he i
    have hit := repeat_at_parameter (hprime i) (hq5 i) (hh i)
      ((le_max_left ..).trans ht.le)
      (he.of_dvd (Finset.dvd_prod_of_mem (fun j => q j*q j-1) (Finset.mem_univ i)))
    have hlt : q i < lucasFibonacciSum (r i+d i*t) := by
      have hqt := (Finset.le_sup (f := q) (Finset.mem_univ i)).trans_lt ((le_max_right ..).trans_lt ht)
      have hdt : t ≤ d i*t := by simpa using Nat.mul_le_mul_right t (hd i)
      exact hqt.trans_le ((by omega : t ≤ r i+d i*t).trans (upper_strict.id_le _))
    exact ⟨hit,fun hu => hlt.ne ((Nat.prime_dvd_prime_iff_eq (hprime i) hu).mp hit)⟩

/-- Every nonconstant affine form has infinitely many prime divisors each of which
divides composite upper values at infinitely many prime parameters. -/
theorem infinite_recurring_divisors_at_prime_parameters (r d : ℕ) (hd : 0 < d) :
    {q : ℕ | q.Prime ∧ {p : ℕ | p.Prime ∧ q ∣ lucasFibonacciSum (r+d*p) ∧
      ¬(lucasFibonacciSum (r+d*p)).Prime}.Infinite}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨q,_,hq,a,L,N,hL,hc,hrecur⟩ :=
    simultaneous_prime_parameter_divisors (k := 1) (fun _ => r) (fun _ => d)
      (fun _ => hd) (fun _ _ _ => Subsingleton.elim _ _) B
  refine ⟨q 0,⟨(hq 0).2,?_⟩,(hq 0).1⟩
  apply Set.infinite_of_forall_exists_gt
  intro K
  obtain ⟨p,hp,hpr,he⟩ := Nat.forall_exists_prime_gt_and_modEq (max N K) hL.ne' hc
  exact ⟨p,⟨hpr,hrecur p ((le_max_left ..).trans_lt hp) he 0⟩,(le_max_right ..).trans_lt hp⟩


#print axioms upper_quadratic_field_period

#print axioms upper_split_prime_parameter

#print axioms simultaneous_prime_parameter_divisors

#print axioms infinite_recurring_divisors_at_prime_parameters

end Arxiv.«2211.10788»
