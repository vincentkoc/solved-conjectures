import Mathlib
import research.arxiv.«2211.10788».LucasFibonacciSmoothBlocks

/-! Finite prime covers on progressions of the upper Hosoya diagonal. -/

namespace Arxiv.«2211.10788»

/-- Every term of the index progression has a divisor in the prescribed prime set. -/
def UpperPrimeCover (S : Finset ℕ) (r d : ℕ) : Prop :=
  (∀ p ∈ S, p.Prime) ∧ ∀ t : ℕ, ∃ p ∈ S, p ∣ lucasFibonacciSum (r+d*t)

private lemma upper_shift_of_fib_zero {p h : ℕ} (hh : p ∣ Nat.fib h) (n : ℕ) :
    p ∣ lucasFibonacciSum (n+h) ↔ p ∣ lucasFibonacciSum n := by
  cases h with
  | zero => simp
  | succ k =>
    have he : lucasFibonacciSum (n+(k+1)) =
        Nat.fib k * lucasFibonacciSum n + Nat.fib (k+1) * lucasFibonacciSum (n+1) := by
      unfold lucasFibonacciSum
      rw [show n+(k+1)=k+n+1 by omega, Nat.fib_add,
        show k+n+1+2=k+(n+2)+1 by omega, Nat.fib_add]
      ring
    have hc : p.Coprime (Nat.fib k) := (Nat.fib_coprime_fib_succ k).symm.of_dvd_left hh
    rw [he,Nat.dvd_add_left (dvd_mul_of_dvd_left hh _),hc.dvd_mul_left]

private lemma cover_rank_spec (p d : ℕ) [NeZero p] :
    0 < fibonacciStepRank p d ∧ p ∣ Nat.fib (d*fibonacciStepRank p d) := by
  unfold fibonacciStepRank
  generalize_proofs h
  exact Nat.find_spec h

-- Two of the first |S|+1 terms share a covering prime.
private lemma cover_repeated_prime {S : Finset ℕ} {r d : ℕ} (hc : UpperPrimeCover S r d) :
    ∃ p ∈ S, ∃ h, 0 < h ∧ h ≤ S.card ∧ p ∣ Nat.fib (d*h) := by
  classical
  choose f hmem hh using hc.2
  let col (i : Fin (S.card+1)) : S := ⟨f i,hmem i⟩
  obtain ⟨i,j,hij,hc'⟩ := Fintype.exists_ne_map_eq_of_card_lt col (by simp)
  have aux (a b : Fin (S.card+1)) (hlt : a < b) (he : col a=col b) :
      ∃ p ∈ S, ∃ h, 0 < h ∧ h ≤ S.card ∧ p ∣ Nat.fib (d*h) := by
    let p := f a
    let : NeZero p := ⟨(hc.1 _ (hmem a)).ne_zero⟩
    have hab : f a=f b := congrArg Subtype.val he
    have hshift : r+d*a.val+d*(b.val-a.val) = r+d*b.val := by
      rw [Nat.add_assoc,← Nat.mul_add,show a.val+(b.val-a.val)=b.val by omega]
    have hbound := b.isLt
    refine ⟨p,hmem a,b.val-a.val,by omega,by omega,?_⟩
    apply common_divisor_lucasFibonacciSum_dvd_fib (hh a)
    rw [hshift,hab]
    exact hh b
  rcases lt_or_gt_of_ne hij with h|h
  · exact aux i j h hc'
  · exact aux j i h hc'.symm

/-- A bounded number of covering primes gives a second hit near the initial term. -/
private lemma short_cover_hit (k : ℕ) (S : Finset ℕ) (r d : ℕ) (hs : S.card ≤ k)
    (hc : UpperPrimeCover S r d) :
    ∃ p ∈ S, p ∣ lucasFibonacciSum r ∧
      ∃ h, 0 < h ∧ h ≤ k.factorial ∧ p ∣ lucasFibonacciSum (r+d*h) := by
  classical
  induction k generalizing S r d with
  | zero =>
    have h := hc.2 0
    simp [Finset.card_eq_zero.mp (by omega : S.card = 0)] at h
  | succ k ih =>
    obtain ⟨q,hq,g,hg,hsize,hfib⟩ := cover_repeated_prime hc
    by_cases hq0 : q ∣ lucasFibonacciSum r
    · refine ⟨q,hq,hq0,g,hg,?_,(upper_shift_of_fib_zero hfib r).mpr hq0⟩
      exact (hsize.trans hs).trans (Nat.self_le_factorial _)
    · -- This residue class avoids q, so one fewer prime must cover it.
      have hco : UpperPrimeCover (S.erase q) r (d*g) := by
        refine ⟨fun p hp => hc.1 p (Finset.mem_of_mem_erase hp),?_⟩
        intro t
        obtain ⟨p,hp,hh⟩ := hc.2 (g*t)
        rw [←Nat.mul_assoc] at hh
        refine ⟨p,Finset.mem_erase.mpr ⟨?_,hp⟩,hh⟩
        rintro rfl
        have hft : p ∣ Nat.fib (d*g*t) :=
          hfib.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))
        exact hq0 ((upper_shift_of_fib_zero hft r).mp hh)
      obtain ⟨p,hp,h0,h,hh,hb,hhit⟩ := ih (S.erase q) r (d*g)
        (by rw [Finset.card_erase_of_mem hq]; omega) hco
      refine ⟨p,Finset.mem_of_mem_erase hp,h0,g*h,Nat.mul_pos hg hh,?_,?_⟩
      · rw [Nat.factorial_succ]
        exact Nat.mul_le_mul (hsize.trans hs) hb
      · simpa [Nat.mul_assoc] using hhit

/-- Every minimal cover by at most k primes is supported in this finite set, independently of the step. -/
def upperCoverCandidates (r k : ℕ) : Finset ℕ :=
  insert 5 ((Finset.Icc 1 k.factorial).biUnion fun e => (progressionPowerCoefficient r e).primeFactors)

private lemma cover_coefficient_pos (r e : ℕ) (he : 0 < e) :
    0 < progressionPowerCoefficient r e := by
  let w : QuadraticAlgebra ℕ 1 1 := QuadraticAlgebra.omega
  let s : QuadraticAlgebra ℕ 1 1 := ⟨3,1⟩
  have hs (n : ℕ) : 0 < (s*w^n).re ∧ 0 < (s*w^n).im := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [pow_succ,←mul_assoc]
      simpa [w,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] using
        (show 0 < (s*w^n).im ∧ 0 < (s*w^n).re+(s*w^n).im by omega)
  let z := s*w^r
  have hz : 0 < z.im := (hs r).2
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  clear he
  change 0 < (z^(n+1)).im
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [pow_succ (a:=z) (n+1),QuadraticAlgebra.im_mul]
    have h := Nat.mul_pos ih hz
    simp only [one_mul]
    omega

private lemma candidate_of_short_rank {p r d k : ℕ} (hp : p.Prime) [NeZero p]
    (hh : ∃ t, p ∣ lucasFibonacciSum (r+d*t)) (he : fibonacciStepRank p d ≤ k.factorial) :
    p ∈ upperCoverCandidates r k := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h5 : p = 5
  · simp [upperCoverCandidates,h5]
  · have hc := (prime_dvd_lucasFibonacciSum_on_progression_iff (p:=p) r d).mp hh
    simp only [if_neg h5] at hc
    have hpos := (cover_rank_spec p d).1
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨_,Finset.mem_Icc.mpr ⟨hpos,he⟩,hp.mem_primeFactors hc.2 (cover_coefficient_pos _ _ hpos).ne'⟩

/-- Intersecting any bounded prime cover with a finite list depending only on its
offset and size keeps it a cover. -/
theorem upper_prime_cover_restrict {S : Finset ℕ} {r d k : ℕ}
    (hS : S.card ≤ k) (hc : UpperPrimeCover S r d) :
    UpperPrimeCover (S ∩ upperCoverCandidates r k) r d := by
  refine ⟨fun p hp => hc.1 p (Finset.mem_inter.mp hp).1,?_⟩
  intro t
  have shifted : UpperPrimeCover S (r+d*t) d := by
    refine ⟨hc.1,fun u => ?_⟩
    simpa [Nat.mul_add,Nat.add_assoc] using hc.2 (t+u)
  obtain ⟨p,hp,hit,h,hh,hs,again⟩ := short_cover_hit k S (r+d*t) d hS shifted
  have prime := hc.1 p hp
  let : NeZero p := ⟨prime.ne_zero⟩
  have hr := (lucasFibonacciSum_dvd_after_hit_iff hit d h).mp again
  exact ⟨p,Finset.mem_inter.mpr ⟨hp,candidate_of_short_rank prime ⟨t,hit⟩
    ((Nat.le_of_dvd hh hr).trans hs)⟩,hit⟩

private lemma candidate_prime {p r k : ℕ} (h : p ∈ upperCoverCandidates r k) : p.Prime := by
  rcases Finset.mem_insert.mp h with rfl|h
  · decide
  · obtain ⟨_,_,hm⟩ := Finset.mem_biUnion.mp h
    exact Nat.prime_of_mem_primeFactors hm

private def coverModulus (r k : ℕ) := ∏ p ∈ upperCoverCandidates r k, p

private lemma coverModulus_pos (r k : ℕ) : 0 < coverModulus r k :=
  Finset.prod_pos fun _ hp => (candidate_prime hp).pos

/-- A single period for testing index steps and progression parameters for a fixed
offset and covering budget. -/
def upperCoverPeriod (r k : ℕ) : ℕ :=
  @fibonacciStepRank (coverModulus r k) 1 ⟨(coverModulus_pos r k).ne'⟩

private lemma cover_period_spec (r k : ℕ) :
    0 < upperCoverPeriod r k ∧ coverModulus r k ∣ Nat.fib (upperCoverPeriod r k) := by
  let : NeZero (coverModulus r k) := ⟨(coverModulus_pos r k).ne'⟩
  simpa [upperCoverPeriod] using cover_rank_spec (coverModulus r k) 1

private lemma candidate_shift {p r k : ℕ} (hp : p ∈ upperCoverCandidates r k) (n s : ℕ) :
    p ∣ lucasFibonacciSum (n + upperCoverPeriod r k*s) ↔ p ∣ lucasFibonacciSum n := by
  apply upper_shift_of_fib_zero
  have hm : p ∣ coverModulus r k := Finset.dvd_prod_of_mem id hp
  exact (hm.trans (cover_period_spec r k).2).trans (Nat.fib_dvd _ _ (dvd_mul_right ..))

private lemma candidate_reduce {p r k : ℕ} (hp : p ∈ upperCoverCandidates r k) (d t : ℕ) :
    p ∣ lucasFibonacciSum (r+d*t) ↔
      p ∣ lucasFibonacciSum (r+(d % upperCoverPeriod r k)*(t % upperCoverPeriod r k)) := by
  let T := upperCoverPeriod r k
  have hd := Nat.mod_add_div d T
  have ht := Nat.mod_add_div t T
  have step : r+d*t = r+(d%T)*t+T*(d/T*t) := by
    calc r+d*t = r+((d%T)+T*(d/T))*t := by rw [hd]
         _ = _ := by ring
  have para : r+(d%T)*t = r+(d%T)*(t%T)+T*((d%T)*(t/T)) := by
    calc r+(d%T)*t = r+(d%T)*((t%T)+T*(t/T)) := by rw [ht]
         _ = _ := by ring
  rw [step,candidate_shift hp,para,candidate_shift hp]

/-- For a fixed offset and prime budget, one finite test decides a prime cover
for every step, including step zero. -/
theorem upper_prime_cover_finite_iff (r d k : ℕ) :
    (∃ S : Finset ℕ, S.card ≤ k ∧ UpperPrimeCover S r d) ↔
      ∃ S ∈ (upperCoverCandidates r k).powerset, S.card ≤ k ∧
        ∀ t < upperCoverPeriod r k, ∃ p ∈ S,
          p ∣ lucasFibonacciSum (r+(d % upperCoverPeriod r k)*t) := by
  let T := upperCoverPeriod r k
  have hT := (cover_period_spec r k).1
  constructor
  · rintro ⟨S,hs,hc⟩
    let A := S ∩ upperCoverCandidates r k
    have hA : A ⊆ upperCoverCandidates r k := Finset.inter_subset_right
    have ha := upper_prime_cover_restrict hs hc
    refine ⟨A,Finset.mem_powerset.mpr hA,(Finset.card_le_card Finset.inter_subset_left).trans hs,?_⟩
    intro t ht
    obtain ⟨p,hp,hit⟩ := ha.2 t
    exact ⟨p,hp,by simpa [Nat.mod_eq_of_lt ht] using (candidate_reduce (hA hp) d t).mp hit⟩
  · rintro ⟨S,hS,hs,hc⟩
    have sub := Finset.mem_powerset.mp hS
    refine ⟨S,hs,fun p hp => candidate_prime (sub hp),?_⟩
    intro t
    obtain ⟨p,hp,hit⟩ := hc (t%T) (Nat.mod_lt _ hT)
    exact ⟨p,hp,(candidate_reduce (sub hp) d t).mpr hit⟩

/-- A single prime divides every term exactly when the initial term and the
Fibonacci number at the step have a common prime divisor. -/
theorem upper_fixed_prime_iff (r d : ℕ) :
    (∃ p : ℕ, p.Prime ∧ ∀ t : ℕ, p ∣ lucasFibonacciSum (r+d*t)) ↔
      1 < (lucasFibonacciSum r).gcd (Nat.fib d) := by
  constructor
  · rintro ⟨p,hp,h⟩
    let : NeZero p := ⟨hp.ne_zero⟩
    have h0 : p ∣ lucasFibonacciSum r := by simpa using h 0
    have h1 : p ∣ lucasFibonacciSum (r+d) := by simpa using h 1
    have hd := common_divisor_lucasFibonacciSum_dvd_fib h0 h1
    exact hp.one_lt.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by
      have hpos := two_pow_le_lucasFibonacciSum_sq r
      exact Nat.pos_of_ne_zero (by rintro he; simp [he] at hpos))) (Nat.dvd_gcd h0 hd))
  · intro hc
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : (lucasFibonacciSum r).gcd (Nat.fib d) ≠ 1)
    obtain ⟨hu,hf⟩ := Nat.dvd_gcd_iff.mp hd
    exact ⟨p,hp,fun t => (upper_shift_of_fib_zero (hf.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))) r).mpr hu⟩

private lemma gcd_two_step_of_cover {r d : ℕ} {S : Finset ℕ} (hs : S.card ≤ 2)
    (hc : UpperPrimeCover S r d) :
    1 < (lucasFibonacciSum r).gcd (Nat.fib (d*2)) := by
  obtain ⟨p,hp,hu,h,hh,hb,hd⟩ := short_cover_hit 2 S r d hs hc
  have prime := hc.1 _ hp
  let : NeZero p := ⟨prime.ne_zero⟩
  have hf := common_divisor_lucasFibonacciSum_dvd_fib hu hd
  have hh' : h ∣ 2 := by change h ≤ 2 at hb; interval_cases h <;> decide
  have h2 := hf.trans (Nat.fib_dvd _ _ (Nat.mul_dvd_mul_left d hh'))
  have hpos : 0 < lucasFibonacciSum r := by
    have hlow := two_pow_le_lucasFibonacciSum_sq r
    exact Nat.pos_of_ne_zero (by rintro he; simp [he] at hlow)
  exact prime.one_lt.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hpos) (Nat.dvd_gcd hu h2))

/-- Two covering primes suffice exactly when both parity classes have a fixed
prime divisor. This reduces the decision to two ordinary gcds. -/
theorem upper_two_prime_cover_iff (r d : ℕ) :
    (∃ S : Finset ℕ, S.card ≤ 2 ∧ UpperPrimeCover S r d) ↔
      1 < (lucasFibonacciSum r).gcd (Nat.fib (d*2)) ∧
      1 < (lucasFibonacciSum (r+d)).gcd (Nat.fib (d*2)) := by
  constructor
  · rintro ⟨S,hs,hc⟩
    refine ⟨gcd_two_step_of_cover hs hc,gcd_two_step_of_cover hs ⟨hc.1,?_⟩⟩
    intro t
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc.2 (t+1)
  · rintro ⟨h0,h1⟩
    obtain ⟨p,hp,he⟩ := (upper_fixed_prime_iff r (d*2)).mpr h0
    obtain ⟨q,hq,ho⟩ := (upper_fixed_prime_iff (r+d) (d*2)).mpr h1
    refine ⟨{p,q},?_,?_,?_⟩
    · exact (Finset.card_insert_le ..).trans (by simp)
    · intro s hs
      simp only [Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl|rfl <;> assumption
    · intro t
      rcases Nat.mod_two_eq_zero_or_one t with ht|ht
      · refine ⟨p,by simp,?_⟩
        convert he (t/2) using 2
        have := Nat.mod_add_div t 2
        rw [Nat.mul_assoc]
        exact congrArg (fun z => r+d*z) (by omega)
      · refine ⟨q,by simp,?_⟩
        convert ho (t/2) using 2
        have := Nat.mod_add_div t 2
        calc r+d*t = r+d*(1+2*(t/2)) := congrArg (fun z => r+d*z) (by omega)
             _ = _ := by ring

/-- The progression starting at 7 with step 34 is covered by 3 and 67,
has no fixed prime divisor, and consists entirely of composite numbers. -/
theorem upper_7_mod_34_composite :
    UpperPrimeCover {3,67} 7 34 ∧
      (¬∃ p : ℕ, p.Prime ∧ ∀ t : ℕ, p ∣ lucasFibonacciSum (7+34*t)) ∧
      ∀ t : ℕ, ¬(lucasFibonacciSum (7+34*t)).Prime := by
  have hf : 3 ∣ Nat.fib 68 ∧ 67 ∣ Nat.fib 68 := by decide
  have hc : UpperPrimeCover {3,67} 7 34 := by
    constructor
    · intro p hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl|rfl <;> decide
    · intro t
      rcases Nat.mod_two_eq_zero_or_one t with ht|ht
      · refine ⟨3,by decide,?_⟩
        rw [show 7+34*t=7+68*(t/2) by omega]
        exact (upper_shift_of_fib_zero (hf.1.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))) 7).mpr (by decide)
      · refine ⟨67,by decide,?_⟩
        rw [show 7+34*t=41+68*(t/2) by omega]
        exact (upper_shift_of_fib_zero (hf.2.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))) 41).mpr (by decide)
  refine ⟨hc,(upper_fixed_prime_iff 7 34).not.mpr (by decide),?_⟩
  intro t hprime
  obtain ⟨p,hp,hd⟩ := hc.2 t
  have he := (Nat.prime_dvd_prime_iff_eq (hc.1 p hp) hprime).mp hd
  rcases Nat.eq_zero_or_pos t with rfl|ht
  · exact (by decide : ¬(lucasFibonacciSum 7).Prime) (by simpa using hprime)
  · have hm : 67 < lucasFibonacciSum (7+34*t) := by
      have h : 67 < lucasFibonacciSum 8 := by decide
      apply h.trans_le
      unfold lucasFibonacciSum
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.fib_mono (by omega)))
        (Nat.fib_mono (by omega))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    omega

#print axioms upper_prime_cover_restrict
#print axioms upper_prime_cover_finite_iff
#print axioms upper_fixed_prime_iff
#print axioms upper_two_prime_cover_iff
#print axioms upper_7_mod_34_composite

end Arxiv.«2211.10788»
