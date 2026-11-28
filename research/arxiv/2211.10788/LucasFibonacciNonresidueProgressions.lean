import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciExcludedPrimes
import research.arxiv.«2211.10788».NeighboringLucasFibonacciPrimes

/-! Quadratic nonresidue prime divisors on progressions of Hosoya upper indices. -/

namespace Arxiv.«2211.10788»

open Finset

/-- Every upper value is a square modulo eleven. -/
theorem upper_square_mod_eleven (n : ℕ) : IsSquare (lucasFibonacciSum n : ZMod 11) := by
  have h : (lucasFibonacciSum n : ZMod 11) = 4^n := by
    induction n using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more n h₀ h₁ =>
      rw [lucas_fibonacci_sum_recurrence, Nat.cast_add, h₁, h₀, pow_add (4 : ZMod 11) n 2,
        pow_succ (4 : ZMod 11) n, show (4 : ZMod 11)^2 = 5 by decide]
      ring
  rw [h]
  exact (show IsSquare (4 : ZMod 11) from ⟨2,by decide⟩).pow n

private lemma odd_cassini (p n : ℕ) :
    (-1 : ZMod p)^n * ((lucasFibonacciSum (n+1) : ZMod p)^2 -
      lucasFibonacciSum n * lucasFibonacciSum (n+1) - (lucasFibonacciSum n : ZMod p)^2) = 11 := by
  induction n with
  | zero => norm_num [lucas_fibonacci_sum_zero, lucas_fibonacci_sum_one]
  | succ n ih =>
    rw [show n.succ + 1 = n + 2 by rfl, lucas_fibonacci_sum_recurrence, Nat.cast_add, pow_succ]
    linear_combination ih

/-- An odd prime divisor outside the squares modulo 11 can only occur at an
even index. Its residue modulo four is forced as well. -/
theorem nonresidue_prime_index {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnr : ¬IsSquare (p : ZMod 11)) (hd : p ∣ lucasFibonacciSum n) :
    Even n ∧ p % 4 = 3 := by
  have ho := hp.odd_of_ne_two hp2
  rw [Nat.odd_iff] at ho
  have h4 : p%4 = 3 := by
    by_contra he
    exact hnr (isSquare_mod_eleven_of_prime_dvd_lucasFibonacciSum hp (by omega) hd)
  refine ⟨?_,h4⟩
  by_contra he
  have hn := Nat.not_even_iff_odd.mp he
  have h11 : p ≠ 11 := by rintro rfl; exact hnr ⟨0, by decide⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4
    (by decide : 11 % 4 = 3) h11).mpr hnr
  have hane : a ≠ 0 := by
    rintro rfl
    exact h11 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
      ((ZMod.natCast_eq_zero_iff 11 p).mp (by simpa using ha)))
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr hd
  have hh := odd_cassini p n
  rw [hn.neg_one_pow,hz] at hh
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(lucasFibonacciSum (n+1) : ZMod p)/a,?_⟩
    field_simp
    push_cast at ha
    linear_combination hh + ha
  exact (by have := ZMod.exists_sq_eq_neg_one_iff.mp hsq; omega)

private def signedUpper (n : ℤ) : ℤ := 2*Int.fib n + Int.fib (n+2)

private lemma signed_nat (n : ℕ) : signedUpper n = lucasFibonacciSum n := by
  simp only [signedUpper,lucasFibonacciSum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.fib_natCast]
  rw [show (n:ℤ)+2 = ((n+2:ℕ):ℤ) by push_cast; rfl, Int.fib_natCast]

private lemma negative_even (a : ℕ) :
    signedUpper (-(2*(a+1):ℕ)) = -(lowerNeighborAtAddTwo (2*a) : ℤ) := by
  have hev (b : ℕ) : Int.fib (-(2*b : ℕ)) = -(Nat.fib (2*b) : ℤ) := by
    rw [Int.fib_neg_natCast, pow_succ, pow_mul]
    norm_num
  have he : -((2*(a+1):ℕ):ℤ)+2 = -((2*a:ℕ):ℤ) := by push_cast; ring
  rw [signedUpper,he,hev,hev,lowerNeighborAtAddTwo,show 2*(a+1) = 2*a+2 by ring]
  push_cast
  ring

private lemma signed_return (m : ℕ) [NeZero m] (s : ℤ) :
    ∃ T > 0, ∀ j : ℕ, (signedUpper (s+(j*T:ℕ)) : ZMod m) = signedUpper s := by
  let state (i : ℕ) : ZMod m × ZMod m := (Int.fib (s+i),Int.fib (s+i+1))
  let step (v : ZMod m × ZMod m) := (v.2,v.1+v.2)
  have hinj : Function.Injective step := by
    rintro ⟨a,b⟩ ⟨c,d⟩ e
    change (b,a+b) = (d,c+d) at e
    obtain ⟨rfl,h⟩ := Prod.mk.inj e
    exact Prod.ext (add_right_cancel h) rfl
  have hs : Function.Semiconj state Nat.succ step := by
    intro n
    dsimp [state,step]
    rw [← add_assoc,show s+n+1+1 = s+n+2 by ring,Int.fib_add_two]
    push_cast
    rfl
  obtain ⟨T,hT,hfix⟩ := hinj.mem_periodicPts (state 0)
  refine ⟨T,hT,fun j => ?_⟩
  have he := (hs.iterate_right (j*T) 0).trans (hfix.const_mul j).eq
  rw [Nat.succ_iterate] at he
  simpa [signedUpper,Int.fib_add_two,state] using
    congrArg (fun v : ZMod m × ZMod m => 2*v.1+(v.1+v.2)) he

private lemma nonsquare_prime_factor (c : ℕ) (hc : ¬IsSquare (c : ZMod 11)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ c ∧ ¬IsSquare (q : ZMod 11) := by
  induction c using Nat.recOnMul with
  | zero => exact (hc ⟨0, by decide⟩).elim
  | one => exact (hc ⟨1, by decide⟩).elim
  | prime p hp => exact ⟨p,hp,dvd_rfl,hc⟩
  | mul a b ia ib =>
    by_cases ha : IsSquare (a : ZMod 11)
    · have hb : ¬IsSquare (b : ZMod 11) := fun h => hc (by simpa only [Nat.cast_mul] using ha.mul h)
      obtain ⟨q,hq,hd,hn⟩ := ib hb
      exact ⟨q,hq,hd.trans (dvd_mul_left ..),hn⟩
    · obtain ⟨q,hq,hd,hn⟩ := ia ha
      exact ⟨q,hq,hd.trans (dvd_mul_right ..),hn⟩

/-- Transport a negative even-index term into the chosen progression. Dividing
out its absolute value leaves a cofactor congruent to −1 modulo 11·B!. -/
private lemma fresh_even_divisor (r d B : ℕ) (hd : 0 < d) :
    ∃ t q : ℕ, B < q ∧ q.Prime ∧ ¬IsSquare (q : ZMod 11) ∧
      q ∣ lucasFibonacciSum (2*(r+d*t)) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let a := d*(r+1)
  let u := lowerNeighborAtAddTwo (2*a)
  let L := 11*B.factorial
  have hu : 0 < u := by
    dsimp [u,lowerNeighborAtAddTwo]
    have := Nat.fib_pos.mpr (show 0 < 2*a+2 by omega)
    omega
  have hL : 0 < L := Nat.mul_pos (by decide) (Nat.factorial_pos _)
  let : NeZero (u*L) := ⟨(Nat.mul_pos hu hL).ne'⟩
  obtain ⟨T,hT,hret⟩ := signed_return (u*L) (-(2*(a+1):ℕ))
  obtain ⟨T,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
  let t := (r+1)*T+(T+1)
  let n := 2*(r+d.succ*t)
  have he : -((2*(a+1):ℕ):ℤ)+((2*(d+1)*(r+2)*T.succ : ℕ):ℤ) = (n:ℤ) := by
    dsimp [n,t,a]
    ring
  have hh := hret (2*(d+1)*(r+2))
  rw [he,signed_nat,negative_even] at hh
  have hdiv : u*L ∣ lucasFibonacciSum n + u := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    push_cast at hh ⊢
    change (lucasFibonacciSum n : ZMod (u*L)) = -(u : ZMod (u*L)) at hh
    rw [hh,neg_add_cancel]
  have hud : u ∣ lucasFibonacciSum n := (Nat.dvd_add_left dvd_rfl).mp
    ((dvd_mul_right u L).trans hdiv)
  obtain ⟨c,hc⟩ := hud
  obtain ⟨j,hj⟩ := hdiv
  have hc1 : c+1 = L*j := Nat.eq_of_mul_eq_mul_left hu (by
    calc u*(c+1) = lucasFibonacciSum n+u := by rw [hc]; ring
         _ = u*(L*j) := hj.trans (Nat.mul_assoc ..))
  have h11 : 11 ∣ c+1 := ⟨B.factorial*j, by rw [hc1]; dsimp [L]; ring⟩
  have hmod := (ZMod.natCast_eq_zero_iff ..).mpr h11
  have hnr : ¬IsSquare (c : ZMod 11) := by
    push_cast at hmod
    rw [eq_neg_of_add_eq_zero_left hmod]
    decide
  obtain ⟨q,hq,hqc,hbad⟩ := nonsquare_prime_factor c hnr
  refine ⟨t,q,?_,hq,hbad,hqc.trans (hc ▸ dvd_mul_left ..)⟩
  by_contra! hle
  have hqL : q ∣ L := (Nat.dvd_factorial hq.pos hle).trans (dvd_mul_left ..)
  have hq1 : q ∣ c+1 := hc1 ▸ hqL.trans (dvd_mul_right ..)
  exact hq.not_dvd_one ((Nat.dvd_add_right hqc).mp hq1)

private lemma preserve_hit {q n : ℕ} (hq : q.Prime) (hdiv : q ∣ lucasFibonacciSum n) :
    ∃ T > 0, ∀ j, q ∣ lucasFibonacciSum (n+j*T) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨T,hT,ht⟩ := signed_return q n
  refine ⟨T,hT,fun j => (ZMod.natCast_eq_zero_iff ..).mp ?_⟩
  have h := ht j
  rw [← Nat.cast_add,signed_nat,signed_nat] at h
  simpa using h.trans (by simpa using (ZMod.natCast_eq_zero_iff ..).mpr hdiv)

private lemma even_family {k : ℕ} (r d : Fin k → ℕ) (hd : ∀ i, 0 < d i) (B : ℕ) :
    ∃ s e : ℕ, 0 < e ∧ ∃ p : Fin k → ℕ, Function.Injective p ∧
      ∀ i, B < p i ∧ (p i).Prime ∧ ¬IsSquare (p i : ZMod 11) ∧
        ∀ j, p i ∣ lucasFibonacciSum (2*(r i+d i*(s+e*j))) := by
  induction k with
  | zero => exact ⟨0,1,by decide,Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨s,e,he,p,hinj,hold⟩ := ih (fun i => r i.succ) (fun i => d i.succ) (fun i => hd i.succ)
    let C := B + ∑ i, p i
    obtain ⟨t,q,hbig,hq,hnr,hhit⟩ :=
      fresh_even_divisor (r 0+d 0*s) (d 0*e) C (Nat.mul_pos (hd 0) he)
    let s' := s+e*t
    have hhit' : q ∣ lucasFibonacciSum (2*(r 0+d 0*s')) := by
      convert hhit using 2
      dsimp [s']
      ring
    obtain ⟨T,hT,hper⟩ := preserve_hit hq hhit'
    have fresh (i : Fin k) : p i < q := by
      have := single_le_sum (s := univ) (f := p) (fun i _ => Nat.zero_le _) (mem_univ i)
      dsimp [C] at hbig
      omega
    refine ⟨s',e*T,Nat.mul_pos he hT,Fin.cons q p,?_,?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [(fresh _).ne']
      · simp [(fresh _).ne]
      · simpa using fun h => hinj h
    · refine Fin.cases ?_ (fun i => ?_)
      · refine ⟨by dsimp [C] at hbig; simpa using (show B < q by omega),
          hq,hnr,fun j => ?_⟩
        simpa only [Fin.cons_zero, show 2*(r 0+d 0*(s'+e*T*j)) =
          2*(r 0+d 0*s')+(2*d 0*e*j)*T by ring] using hper (2*d 0*e*j)
      · obtain ⟨hB,hp,hn,hj⟩ := hold i
        refine ⟨hB,hp,hn,fun j => ?_⟩
        simpa only [Fin.cons_succ,show s'+e*T*j = s+e*(t+T*j) by dsimp [s']; ring] using hj (t+T*j)

/-- A finite family of positive-step affine indices can carry distinct, arbitrarily
large nonsquare-mod-11 prime divisors throughout a common parameter progression
exactly when the indices can all be even at a common parameter. Repetitions of
an index form request several distinct prime divisors of the same term. -/
theorem nonresidue_divisor_patterns_iff {k : ℕ} (r d : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (B : ℕ) :
    (∃ t : ℕ, ∀ i, Even (r i+d i*t)) ↔
    ∃ s e : ℕ, 0 < e ∧ ∃ p : Fin k → ℕ, Function.Injective p ∧
      ∀ i, B < p i ∧ (p i).Prime ∧ p i % 4 = 3 ∧ ¬IsSquare (p i : ZMod 11) ∧
        ∀ j, p i ∣ lucasFibonacciSum (r i+d i*(s+e*j)) := by
  constructor
  · rintro ⟨t,h⟩
    choose a ha using h
    obtain ⟨s,e,he,p,hinj,hp⟩ := even_family a d hd (max B 2)
    refine ⟨t+2*s,2*e,by omega,p,hinj,fun i => ?_⟩
    obtain ⟨hB,hprime,hnr,hdiv⟩ := hp i
    have h4 := (nonresidue_prime_index hprime (by omega) hnr (hdiv 0)).2
    refine ⟨by omega,hprime,h4,hnr,fun j => ?_⟩
    convert hdiv j using 2
    linear_combination ha i
  · rintro ⟨s,e,_,p,_,hp⟩
    refine ⟨s,fun i => ?_⟩
    obtain ⟨_,hq,h4,hnr,hdiv⟩ := hp i
    simpa using (nonresidue_prime_index hq (by omega) hnr (hdiv 0)).1

/-- The nonsquare-mod-11 prime divisors on a progression are unbounded exactly
when the progression meets an even index. Each prime in the set divides a
composite and never equals any upper value. -/
theorem infinite_nonvalue_prime_divisors_iff (r d : ℕ) (hd : 0 < d) :
    {q : ℕ | q.Prime ∧ q % 4 = 3 ∧ ¬IsSquare (q : ZMod 11) ∧
      (∀ n, lucasFibonacciSum n ≠ q) ∧ ∃ t, ¬(lucasFibonacciSum (r+d*t)).Prime ∧
        q ∣ lucasFibonacciSum (r+d*t)}.Infinite ↔ ∃ t, Even (r+d*t) := by
  constructor
  · intro h
    obtain ⟨q,hq,h4,hnr,_,t,_,hdiv⟩ := h.nonempty
    exact ⟨t,(nonresidue_prime_index hq (by omega) hnr hdiv).1⟩
  · rintro ⟨t,ht⟩
    apply Set.infinite_of_forall_exists_gt
    intro B
    obtain ⟨s,e,_,p,_,hp⟩ :=
      (nonresidue_divisor_patterns_iff (fun _ : Fin 1 => r) (fun _ => d) (fun _ => hd) B).mp
        ⟨t,fun _ => ht⟩
    obtain ⟨hB,hq,h4,hnr,hdiv⟩ := hp 0
    have absent (n : ℕ) : lucasFibonacciSum n ≠ p 0 := fun he =>
      hnr (he ▸ upper_square_mod_eleven n)
    have hs : p 0 ∣ lucasFibonacciSum (r+d*s) := by simpa using hdiv 0
    refine ⟨p 0,⟨hq,h4,hnr,absent,s,fun hprime => ?_,hs⟩,hB⟩
    exact absent _ ((hprime.eq_one_or_self_of_dvd _ hs).resolve_left hq.ne_one).symm

#print axioms nonresidue_divisor_patterns_iff
#print axioms infinite_nonvalue_prime_divisors_iff

#print axioms upper_square_mod_eleven
#print axioms nonresidue_prime_index

end Arxiv.«2211.10788»
