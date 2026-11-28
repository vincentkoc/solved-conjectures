import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciExcludedPrimes
import research.arxiv.«2211.10788».NeighboringLucasFibonacciPrimes
import research.arxiv.«2211.10788».LucasFibonacciSmoothBlocks

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
    ∃ q : ℕ, q.Prime ∧ Odd (c.factorization q) ∧ ¬IsSquare (q : ZMod 11) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by decide⟩
  by_contra! h
  apply hc
  rw [← Nat.prod_factorization_pow_eq_self hc0]
  simp only [Finsupp.prod,Nat.cast_prod,Nat.cast_pow]
  apply Finset.isSquare_prod
  intro q hq
  have hp : q.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)
  rcases (c.factorization q).even_or_odd with he|ho
  · obtain ⟨a,ha⟩ := he
    exact ⟨(q:ZMod 11)^a, by rw [ha,pow_add]⟩
  · exact (h q hp ho).pow _

private lemma dvd_of_odd_val {q N : ℕ} (h : Odd (N.factorization q)) : q ∣ N := by
  by_contra hn
  rw [Nat.factorization_eq_zero_of_not_dvd hn] at h
  simp at h

/-- Transport a negative even-index term into the chosen progression. Dividing
out its absolute value leaves a cofactor congruent to −1 modulo 11·B!. -/
private lemma fresh_even_divisor (r d B : ℕ) (hd : 0 < d) :
    ∃ t q : ℕ, B < q ∧ q.Prime ∧ ¬IsSquare (q : ZMod 11) ∧
      Odd ((lucasFibonacciSum (2*(r+d*t))).factorization q) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let a := d*(r+1)
  let u := lowerNeighborAtAddTwo (2*a)
  let L := 11*(max B u).factorial
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
  have h11 : 11 ∣ c+1 := ⟨(max B u).factorial*j, by rw [hc1]; dsimp [L]; ring⟩
  have hmod := (ZMod.natCast_eq_zero_iff ..).mpr h11
  have hnr : ¬IsSquare (c : ZMod 11) := by
    push_cast at hmod
    rw [eq_neg_of_add_eq_zero_left hmod]
    decide
  obtain ⟨q,hq,hodd,hbad⟩ := nonsquare_prime_factor c hnr
  have hqc := dvd_of_odd_val hodd
  have hlarge : max B u < q := by
    by_contra! hle
    have hqL : q ∣ L := (Nat.dvd_factorial hq.pos hle).trans (dvd_mul_left ..)
    have hq1 : q ∣ c+1 := hc1 ▸ hqL.trans (dvd_mul_right ..)
    exact hq.not_dvd_one ((Nat.dvd_add_right hqc).mp hq1)
  refine ⟨t,q,by omega,hq,hbad,?_⟩
  change Odd ((lucasFibonacciSum n).factorization q)
  have hc0 : c ≠ 0 := by rintro rfl; exact hnr ⟨0, by decide⟩
  rw [hc,Nat.factorization_mul hu.ne' hc0,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hu (by omega)),zero_add]
  exact hodd

private lemma upper_positive (n : ℕ) : 0 < lucasFibonacciSum n := by
  have := Nat.fib_pos.mpr (by omega : 0 < n+2)
  unfold lucasFibonacciSum
  omega

/-- Returning modulo the next prime power preserves the exact valuation. -/
private lemma preserve_valuation {q : ℕ} (n : ℕ) (hq : q.Prime) :
    ∃ T > 0, ∀ j, (lucasFibonacciSum (n+j*T)).factorization q =
      (lucasFibonacciSum n).factorization q := by
  let v := (lucasFibonacciSum n).factorization q
  let m := q^(v+1)
  let : NeZero m := ⟨pow_ne_zero _ hq.ne_zero⟩
  obtain ⟨T,hT,ht⟩ := signed_return m n
  refine ⟨T,hT,fun j => ?_⟩
  have h := ht j
  rw [← Nat.cast_add,signed_nat,signed_nat] at h
  have hmod : lucasFibonacciSum (n+j*T) ≡ lucasFibonacciSum n [MOD m] :=
    (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using h)
  have transfer (b : ℕ) (hb : b ≤ v+1) :
      b ≤ (lucasFibonacciSum (n+j*T)).factorization q ↔ b ≤ v := by
    rw [← hq.pow_dvd_iff_le_factorization (upper_positive _).ne',
      ← hq.pow_dvd_iff_le_factorization (upper_positive n).ne']
    have hc := hmod.of_dvd (show q^b ∣ m from pow_dvd_pow q hb)
    simp only [← Nat.modEq_zero_iff_dvd]
    exact ⟨fun he => hc.symm.trans he, fun he => hc.trans he⟩
  have hlo := (transfer v (by omega)).mpr le_rfl
  have hhi := (transfer (v+1) le_rfl).not.mpr (by omega)
  change _ = v
  omega

private lemma even_family {k : ℕ} (r d : Fin k → ℕ) (hd : ∀ i, 0 < d i) (B : ℕ) :
    ∃ s e : ℕ, 0 < e ∧ ∃ p : Fin k → ℕ, Function.Injective p ∧
      ∀ i, B < p i ∧ (p i).Prime ∧ ¬IsSquare (p i : ZMod 11) ∧
        ∃ v : ℕ, Odd v ∧ ∀ j, (lucasFibonacciSum (2*(r i+d i*(s+e*j)))).factorization (p i) = v := by
  induction k with
  | zero => exact ⟨0,1,by decide,Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨s,e,he,p,hinj,hold⟩ := ih (fun i => r i.succ) (fun i => d i.succ) (fun i => hd i.succ)
    let C := B + ∑ i, p i
    obtain ⟨t,q,hbig,hq,hnr,hhit⟩ :=
      fresh_even_divisor (r 0+d 0*s) (d 0*e) C (Nat.mul_pos (hd 0) he)
    let s' := s+e*t
    have hhit' : Odd ((lucasFibonacciSum (2*(r 0+d 0*s'))).factorization q) := by
      simpa only [show r 0+d 0*s' = r 0+d 0*s+d 0*e*t by dsimp [s']; ring] using hhit
    obtain ⟨T,hT,hper⟩ := preserve_valuation (2*(r 0+d 0*s')) hq
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
          hq,hnr,_,hhit',fun j => ?_⟩
        simpa only [Fin.cons_zero, show 2*(r 0+d 0*(s'+e*T*j)) =
          2*(r 0+d 0*s')+(2*d 0*e*j)*T by ring] using hper (2*d 0*e*j)
      · obtain ⟨hB,hp,hn,v,hv,hj⟩ := hold i
        refine ⟨hB,hp,hn,v,hv,fun j => ?_⟩
        simpa only [Fin.cons_succ,show s'+e*T*j = s+e*(t+T*j) by dsimp [s']; ring] using hj (t+T*j)

/-- A finite family of positive-step affine indices can have distinct arbitrarily
large primes, nonsquare modulo 11, occurring to fixed odd valuations on a common progression
exactly when the indices can all be even at a common parameter. Repetitions of
an index form request several distinct prime divisors of the same term. -/
theorem nonresidue_divisor_patterns_iff {k : ℕ} (r d : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (B : ℕ) :
    (∃ t : ℕ, ∀ i, Even (r i+d i*t)) ↔
    ∃ s e : ℕ, 0 < e ∧ ∃ p : Fin k → ℕ, Function.Injective p ∧
      ∀ i, B < p i ∧ (p i).Prime ∧ p i % 4 = 3 ∧ ¬IsSquare (p i : ZMod 11) ∧
        ∃ v : ℕ, Odd v ∧ ∀ j, (lucasFibonacciSum (r i+d i*(s+e*j))).factorization (p i) = v := by
  constructor
  · rintro ⟨t,h⟩
    choose a ha using h
    obtain ⟨s,e,he,p,hinj,hp⟩ := even_family a d hd (max B 2)
    refine ⟨t+2*s,2*e,by omega,p,hinj,fun i => ?_⟩
    obtain ⟨hB,hprime,hnr,v,hv,hval⟩ := hp i
    have h4 := (nonresidue_prime_index hprime (by omega) hnr (dvd_of_odd_val ((hval 0).symm ▸ hv))).2
    refine ⟨by omega,hprime,h4,hnr,v,hv,fun j => ?_⟩
    rw [show r i+d i*(t+2*s+2*e*j) = 2*(a i+d i*(s+e*j)) by linear_combination ha i]
    exact hval j
  · rintro ⟨s,e,_,p,_,hp⟩
    refine ⟨s,fun i => ?_⟩
    obtain ⟨_,hq,h4,hnr,v,hv,hval⟩ := hp i
    simpa using (nonresidue_prime_index hq (by omega) hnr (dvd_of_odd_val ((hval 0).symm ▸ hv))).1

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
    obtain ⟨hB,hq,h4,hnr,v,hv,hval⟩ := hp 0
    have absent (n : ℕ) : lucasFibonacciSum n ≠ p 0 := fun he =>
      hnr (he ▸ upper_square_mod_eleven n)
    have hs : p 0 ∣ lucasFibonacciSum (r+d*s) := by
      simpa using dvd_of_odd_val ((hval 0).symm ▸ hv)
    refine ⟨p 0,⟨hq,h4,hnr,absent,s,fun hprime => ?_,hs⟩,hB⟩
    exact absent _ ((hprime.eq_one_or_self_of_dvd _ hs).resolve_left hq.ne_one).symm

private lemma large_prime_cannot_hit_two_shifts {q : ℕ} (hq : q.Prime)
    (s a b H : ℕ) (ha : a < b) (hb : b ≤ H) (hlarge : Nat.fib H < q)
    (h₁ : q ∣ lucasFibonacciSum (s+a)) (h₂ : q ∣ lucasFibonacciSum (s+b)) : False := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have hh : q ∣ Nat.fib (b-a) := common_divisor_lucasFibonacciSum_dvd_fib h₁ (by
    simpa only [show s+a+(b-a) = s+b by omega] using h₂)
  have hbound := Nat.le_of_dvd (Nat.fib_pos.mpr (by omega)) hh
  exact hlarge.not_ge (hbound.trans (Nat.fib_mono (by omega)))

/-- For distinct fixed shifts with a simultaneous even parameter, one subprogression
makes every nonempty subset product nonsquare at every step. An arbitrarily large
nonresidue prime with odd valuation witnesses each failed square condition. -/
theorem shifted_upper_products_nonsquare {k : ℕ} (r d B : ℕ) (hd : 0 < d)
    (h : Fin k → ℕ) (hdist : Function.Injective h)
    (heven : ∃ t : ℕ, ∀ i, Even (r+h i+d*t)) :
    ∃ s e : ℕ, 0 < e ∧ ∀ (j : ℕ) (S : Finset (Fin k)), S.Nonempty →
      let N := ∏ i ∈ S, lucasFibonacciSum (r+h i+d*(s+e*j))
      ¬ IsSquare N ∧ ∃ q : ℕ, B < q ∧ q.Prime ∧ ¬IsSquare (q : ZMod 11) ∧
        Odd (N.factorization q) := by
  let H := ∑ i, h i
  have hh (i : Fin k) : h i ≤ H := single_le_sum (fun i _ => Nat.zero_le (h i)) (mem_univ i)
  obtain ⟨s,e,he,p,_,hp⟩ :=
    (nonresidue_divisor_patterns_iff (fun i => r+h i) (fun _ => d) (fun _ => hd)
      (max B (Nat.fib H))).mp heven
  refine ⟨s,e,he,fun j S hS => ?_⟩
  obtain ⟨i,hi⟩ := hS
  obtain ⟨hbig,hq,_,hnr,v,hodd,hval⟩ := hp i
  let a (l : Fin k) := lucasFibonacciSum (r+h l+d*(s+e*j))
  change ¬IsSquare (∏ l ∈ S, a l) ∧ _
  have hpriv (l : Fin k) (hl : l ≠ i) : ¬p i ∣ a l := by
    intro hdv
    let b := r+d*(s+e*j)
    have h₁ : p i ∣ lucasFibonacciSum (b+h i) := by
      simpa only [b,add_right_comm] using dvd_of_odd_val ((hval j).symm ▸ hodd)
    have h₂ : p i ∣ lucasFibonacciSum (b+h l) := by
      simpa only [a,b,add_right_comm] using hdv
    have hne : h l ≠ h i := fun hli => hl (hdist hli)
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · exact large_prime_cannot_hit_two_shifts hq b _ _ H hlt (hh i) (by omega) h₂ h₁
    · exact large_prime_cannot_hit_two_shifts hq b _ _ H hgt (hh l) (by omega) h₁ h₂
  have hprodval : (∏ l ∈ S, a l).factorization (p i) = v := by
    rw [Nat.factorization_prod (fun l _ => (upper_positive _).ne')]
    simp only [Finsupp.finsetSum_apply]
    rw [sum_eq_single_of_mem i hi (fun l _ hl => Nat.factorization_eq_zero_of_not_dvd (hpriv l hl))]
    exact hval j
  have hP : Odd ((∏ l ∈ S, a l).factorization (p i)) := hprodval ▸ hodd
  refine ⟨?_,p i,by omega,hq,hnr,hP⟩
  rintro ⟨x,hx⟩
  have hpos : 0 < ∏ l ∈ S, a l := prod_pos (fun l _ => upper_positive _)
  have hx0 : x ≠ 0 := by rintro rfl; simp [hx] at hpos
  rw [hx,Nat.factorization_mul hx0 hx0,Finsupp.add_apply] at hP
  obtain ⟨m,hm⟩ := hP
  omega

#print axioms upper_square_mod_eleven
#print axioms nonresidue_prime_index
#print axioms nonresidue_divisor_patterns_iff
#print axioms infinite_nonvalue_prime_divisors_iff
#print axioms shifted_upper_products_nonsquare

end Arxiv.«2211.10788»
