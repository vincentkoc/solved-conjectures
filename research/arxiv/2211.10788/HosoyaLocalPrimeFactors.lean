import HosoyaPrimeIndexFrobenius
import HosoyaReducedPrimeCofactors
import LucasFibonacciPrimeIndices

/-! Arbitrarily many large factors in a prescribed prime-index class. -/

namespace Arxiv.«2211.10788»

private lemma term_pos (n : ℕ) : 0 < lucasFibonacciSum n := by
  have := Nat.fib_pos.mpr (by omega : 0<n+2)
  unfold lucasFibonacciSum
  omega

private lemma square_one {p C : ℕ} (hC : C ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ C → p ∣ q*q-1) : (C:ZMod p)^2=1 := by
  induction C using induction_on_primes with
  | zero => contradiction
  | one => simp
  | prime_mul q c hq ih =>
    have hh := ih (right_ne_zero_of_mul hC) (fun t ht hd => h t ht (hd.trans (dvd_mul_left ..)))
    have he := (Nat.modEq_iff_dvd' (by nlinarith [hq.two_le] : 1≤q*q)).mpr (h q hq (dvd_mul_right ..))
    have hq' : (q:ZMod p)^2=1 := by
      simpa [pow_two] using ((ZMod.natCast_eq_natCast_iff 1 (q*q) p).mpr he).symm
    rw [Nat.cast_mul,mul_pow,hq',hh,one_mul]

private theorem escaping_factor {p A C : ℕ} (hp : p.Prime) (hbig : max (A^2) 16<p)
    (hA : A.Coprime 6) (hu : lucasFibonacciSum p=A*C) :
    ∃ q, q.Prime ∧ q ∣ C ∧ ¬p ∣ q*q-1 := by
  by_contra! none
  have hc : C≠0 := by intro h; have := term_pos p; simp [h] at hu; omega
  have hsq := square_one hc none
  have hmod : (lucasFibonacciSum p:ZMod p)^2=(A:ZMod p)^2 := by rw [hu,Nat.cast_mul,mul_pow,hsq,mul_one]
  have small {b : ℕ} (hb : b≤4) (he : (A:ZMod p)^2=(b:ZMod p)^2) : A=b := by
    have h := (ZMod.natCast_eq_natCast_iff (A^2) (b^2) p).mp (by simpa only [Nat.cast_pow] using he)
    apply Nat.pow_left_injective (by decide : 2≠0)
    exact h.eq_of_lt_of_lt (by omega) (lt_of_le_of_lt (Nat.pow_le_pow_left hb 2) (by omega : 4^2<p))
  rcases upper_at_prime_frobenius hp (by omega) with h|h
  · have e : A=4 := small (by decide) (by simpa [h] using hmod.symm)
    exact (by decide : ¬Nat.Coprime 4 6) (e ▸ hA)
  · have e : A=3 := small (by decide) (by simpa [h] using hmod.symm)
    exact (by decide : ¬Nat.Coprime 3 6) (e ▸ hA)

private lemma upper_periodic_dvd {q : ℕ} (hq : q.Prime) (h5 : 5<q) {t p : ℕ}
    (h : t ≡ p [MOD q*q-1]) (hit : q ∣ lucasFibonacciSum p) : q ∣ lucasFibonacciSum t := by
  let e := q*q-1
  have fold (n : ℕ) : (lucasFibonacciSum n)%q=(lucasFibonacciSum (n%e))%q := by
    have per : Function.Periodic (fun u => (lucasFibonacciSum u)%q) e :=
      fun u => upper_quadratic_field_period hq h5 u
    have eq := per.nat_mul (n/e) (n%e)
    change (lucasFibonacciSum (n%e+n/e*e))%q=_ at eq
    rwa [Nat.mul_comm (n/e) e,Nat.mod_add_div] at eq
  exact Nat.dvd_of_mod_eq_zero (by rw [fold t,show t%e=p%e from h,←fold p,Nat.mod_eq_zero_of_dvd hit])

private theorem refine_once {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m)
    (good : ∀ n, n.Prime → n ≡ a [MOD m] → (lucasFibonacciSum n).Coprime 6) (B : ℕ) :
    ∃ b L q : ℕ, 0<L ∧ m ∣ L ∧ b ≡ a [MOD m] ∧ b.Coprime L ∧
      B<q ∧ q.Prime ∧ ∀ t, t ≡ b [MOD L] → q ∣ lucasFibonacciSum t := by
  let S := (Finset.range (max 5 B+1)).filter Nat.Prime
  have primes : ∀ q ∈ S, Nat.Prime q := fun q h => (Finset.mem_filter.mp h).2
  obtain ⟨s,K,A,_,hs,hsm,hK,hmK,hsK,hA,hall⟩ :=
    upper_prime_index_fixed_cofactor S primes hm ha 0
  have hA6 := (good s hs hsm).of_dvd_left hA
  obtain ⟨p,hbig,hp,hpK⟩ := Nat.forall_exists_prime_gt_and_modEq (max (A^2) 16) hK.ne' hsK
  obtain ⟨C,hu,havoid⟩ := hall p hpK
  obtain ⟨q,hq,hqc,hord⟩ := escaping_factor hp hbig hA6 hu
  have large : max 5 B<q := by
    by_contra! small
    exact havoid q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hq⟩) hqc
  let d := q*q-1
  have hd : 0<d := by dsimp [d]; have := hq.two_le; nlinarith [Nat.sub_add_cancel (show 1≤q*q by nlinarith)]
  have hpa := (hpK.of_dvd hmK).trans hsm
  have cp : p.Coprime m := hpa.gcd_eq.trans ha
  refine ⟨p,m*d,q,Nat.mul_pos hm hd,dvd_mul_right ..,hpa,
    cp.mul_right (hp.coprime_iff_not_dvd.mpr hord),by omega,hq,?_⟩
  intro t ht
  apply upper_periodic_dvd hq (by omega) (ht.of_dvd (dvd_mul_left ..))
  exact hu ▸ hqc.trans (dvd_mul_left ..)

/-- Every reduced class on which the prime-index upper terms are coprime to
six has a reduced subclass forcing any requested number of large, distinct
prime factors at every index. -/
theorem upper_many_factors_in_prime_class {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m)
    (good : ∀ n, n.Prime → n ≡ a [MOD m] → (lucasFibonacciSum n).Coprime 6)
    (B k : ℕ) :
    ∃ b L : ℕ, 0<L ∧ m ∣ L ∧ b ≡ a [MOD m] ∧ b.Coprime L ∧
      ∃ S : Finset ℕ, S.card=k ∧ ∀ q ∈ S, B<q ∧ q.Prime ∧
        ∀ t, t ≡ b [MOD L] → q ∣ lucasFibonacciSum t := by
  classical
  induction k with
  | zero => exact ⟨a,m,hm,dvd_rfl,Nat.ModEq.refl _,ha,∅,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨b,L,hL,hmL,hb,hunit,S,hcard,hs⟩ := ih
    have nextgood (n : ℕ) (hp : n.Prime) (hn : n ≡ b [MOD L]) :=
      good n hp ((hn.of_dvd hmL).trans hb)
    obtain ⟨c,D,q,hD,hLD,hc,hu,hlarge,hq,hit⟩ :=
      refine_once hL hunit nextgood (max B (S.sup id))
    have hnew : q∉S := by
      intro h
      have lb : q≤S.sup id := Finset.le_sup (f:=id) h
      omega
    refine ⟨c,D,hD,hmL.trans hLD,(hc.of_dvd hmL).trans hb,hu,insert q S,by simp [hnew,hcard],?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact ⟨by omega,hq,hit⟩
    · obtain ⟨hb',hp',hh⟩ := hs z hz
      exact ⟨hb',hp',fun t ht => hh t ((ht.of_dvd hLD).trans hc)⟩


/-- A reduced class intersects the period-120 sieve survivors precisely when
it contains a reduced refinement with any prescribed number of fixed large
prime factors, still coprime to the entire Fibonacci sieve modulus. -/
theorem upper_surviving_class_many_factors_iff {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m)
    (B k : ℕ) :
    (a ≡ 41 [MOD m.gcd 120] ∨ a ≡ 89 [MOD m.gcd 120]) ↔
    ∃ b L : ℕ, 0<L ∧ m ∣ L ∧ 120 ∣ L ∧ b ≡ a [MOD m] ∧ b.Coprime L ∧
      (∀ t, t ≡ b [MOD L] → (lucasFibonacciSum t).Coprime (Nat.fib 120)) ∧
      ∃ S : Finset ℕ, S.card=k ∧ ∀ q ∈ S, B<q ∧ q.Prime ∧
        ∀ t, t ≡ b [MOD L] → q ∣ lucasFibonacciSum t := by
  have h6 : 6 ∣ Nat.fib 120 := (by decide : 6 ∣ Nat.fib 12).trans (Nat.fib_dvd _ _ (by decide))
  constructor
  · intro hh
    obtain ⟨r,hr,hcompat⟩ : ∃ r : ℕ, (r=41 ∨ r=89) ∧ a ≡ r [MOD m.gcd 120] := by
      rcases hh with h|h
      · exact ⟨41,Or.inl rfl,h⟩
      · exact ⟨89,Or.inr rfl,h⟩
    obtain ⟨z,hzm,hzr⟩ := Nat.chineseRemainder' hcompat
    have rr : r.Coprime 120 := by rcases hr with rfl|rfl <;> decide
    have hz : z.Coprime (m*120) := (show z.Coprime m from hzm.gcd_eq.trans ha).mul_right
      (show z.Coprime 120 from hzr.gcd_eq.trans rr)
    have good (n : ℕ) (he : n ≡ z [MOD m*120]) :
        (lucasFibonacciSum n).Coprime (Nat.fib 120) := by
      have hn := (he.of_dvd (dvd_mul_left 120 m)).trans hzr
      apply (upper_period_120_coprime_iff n (hn.gcd_eq.trans rr)).mpr
      rcases hr with rfl|rfl
      · exact Or.inl hn
      · exact Or.inr hn
    obtain ⟨b,L,hL,hdiv,hb,hunit,S,hcard,hs⟩ :=
      upper_many_factors_in_prime_class (Nat.mul_pos hm (by decide)) hz
        (fun n _ he => (good n he).of_dvd_right h6) B k
    exact ⟨b,L,hL,(dvd_mul_right ..).trans hdiv,(dvd_mul_left ..).trans hdiv,
      (hb.of_dvd (dvd_mul_right ..)).trans hzm,hunit,
      fun t ht => good t ((ht.of_dvd hdiv).trans hb),S,hcard,hs⟩
  · rintro ⟨b,L,_,hmL,h120,hb,hu,hg,_⟩
    have h := (upper_period_120_coprime_iff b (hu.of_dvd_right h120)).mp (hg b (Nat.ModEq.refl _))
    have transfer {r : ℕ} (he : b ≡ r [MOD 120]) : a ≡ r [MOD m.gcd 120] :=
      (hb.symm.of_dvd (Nat.gcd_dvd_left ..)).trans (he.of_dvd (Nat.gcd_dvd_right ..))
    rcases h with h|h
    · exact Or.inl (transfer (r:=41) h)
    · exact Or.inr (transfer (r:=89) h)

/-- An incompatible prime-index progression has no prime upper values
beyond the two small prime indices in the pinned example. -/
theorem upper_prime_value_in_class {a m p : ℕ} (hp : p.Prime) (hpa : p ≡ a [MOD m])
    (hu : (lucasFibonacciSum p).Prime) :
    p=2 ∨ p=5 ∨ a ≡ 41 [MOD m.gcd 120] ∨ a ≡ 89 [MOD m.gcd 120] := by
  rcases upper_prime_value_at_prime_index hp hu with h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ((hpa.symm.of_dvd (Nat.gcd_dvd_left ..)).trans
      ((show p ≡ 41 [MOD 120] from h).of_dvd (Nat.gcd_dvd_right ..)))))
  · exact Or.inr (Or.inr (Or.inr ((hpa.symm.of_dvd (Nat.gcd_dvd_left ..)).trans
      ((show p ≡ 89 [MOD 120] from h).of_dvd (Nat.gcd_dvd_right ..)))))

#print axioms upper_surviving_class_many_factors_iff
#print axioms upper_prime_value_in_class

#print axioms upper_many_factors_in_prime_class

end Arxiv.«2211.10788»
