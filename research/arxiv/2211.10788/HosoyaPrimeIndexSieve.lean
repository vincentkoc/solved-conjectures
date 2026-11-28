import HosoyaPrimeParameterClasses

/-! Prime indices passing the Fibonacci-period 120 sieve, and examples of
divisors occurring at a unique prime index. -/

namespace Arxiv.«2211.10788»

private def fastUpper (n : ℕ) : ℕ :=
  3*(Nat.fastFibAux n).1+(Nat.fastFibAux n).2

private theorem fastUpper_eq (n : ℕ) : fastUpper n = lucasFibonacciSum n := by
  simp [fastUpper,Nat.fastFibAux_eq,lucasFibonacciSum,Nat.fib_add_two]
  omega

private def fastF (n : ℕ) := (Nat.fastFibAux n).1

private lemma fastF_eq (n : ℕ) : fastF n=Nat.fib n := by simp [fastF,Nat.fastFibAux_eq]

private lemma certified_rank (m E : ℕ) [NeZero m] (he : 0<E) (hE : m ∣ fastF E)
    (hsmall : ∀ i : Fin E, (0 < i.val) → ¬ m ∣ fastF i.val) : fibonacciStepRank m 1=E := by
  unfold fibonacciStepRank
  apply (Nat.find_eq_iff _).mpr
  refine ⟨⟨he,by simpa [fastF_eq] using hE⟩,?_⟩
  intro i hi h
  exact hsmall ⟨i,hi⟩ h.1 (by simpa [fastF_eq] using h.2)

private lemma unique_prime_hit {p s E : ℕ} [NeZero p] (hq : s.Prime)
    (hg : s.gcd E = s) (hr : fibonacciStepRank p 1 = E) (hs : p ∣ fastUpper s) (q : ℕ) :
    q.Prime ∧ p ∣ lucasFibonacciSum q ↔ q=s := by
  have hit : p ∣ lucasFibonacciSum (0+1*s) := by simpa [fastUpper_eq] using hs
  have hn : ¬s.Coprime (fibonacciStepRank p 1) := by
    rw [Nat.coprime_iff_gcd_eq_one,hr,hg]
    exact hq.ne_one
  constructor
  · rintro ⟨prime,h⟩
    simpa only [hr,hg] using upper_singular_prime_parameter hit hn prime (by simpa using h)
  · rintro rfl
    exact ⟨hq,by simpa using hit⟩

/-- The primes 463 and 487 each have just one prime-index occurrence, even
though both recur at infinitely many unrestricted indices. -/
theorem prime_indices_for_463_and_487 (q : ℕ) :
    (q.Prime ∧ 463 ∣ lucasFibonacciSum q ↔ q=29) ∧
    (q.Prime ∧ 487 ∣ lucasFibonacciSum q ↔ q=61) := by
  constructor
  · exact unique_prime_hit (E:=464) (by decide) (by decide)
      (certified_rank 463 464 (by decide) (by decide) (by decide +kernel)) (by decide) q
  · exact unique_prime_hit (E:=488) (by decide) (by decide)
      (certified_rank 487 488 (by decide) (by decide) (by decide +kernel)) (by decide) q

private lemma return_mod (m L : ℕ) (hm : m ∣ Nat.fib L) (n : ℕ) :
    m ∣ lucasFibonacciSum n ↔ m ∣ lucasFibonacciSum (n%L) := by
  have per : Function.Periodic (fun t => m ∣ lucasFibonacciSum t) L :=
    fun t => propext (lucasFibonacciSum_dvd_shift_iff (s:=t) hm)
  have eq := per.nat_mul (n/L) (n%L)
  change (m ∣ lucasFibonacciSum (n%L+(n/L)*L)) = _ at eq
  rw [Nat.mul_comm (n/L) L,Nat.mod_add_div] at eq
  exact Iff.of_eq eq

/-- Folding indices modulo L preserves the entire gcd with F_L. -/
theorem upper_gcd_return (L n : ℕ) :
    (lucasFibonacciSum n).gcd (Nat.fib L) =
      (lucasFibonacciSum (n%L)).gcd (Nat.fib L) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd ((return_mod _ L (Nat.gcd_dvd_right ..) n).mp (Nat.gcd_dvd_left ..))
      (Nat.gcd_dvd_right ..)
  · exact Nat.dvd_gcd ((return_mod _ L (Nat.gcd_dvd_right ..) n).mpr (Nat.gcd_dvd_left ..))
      (Nat.gcd_dvd_right ..)

private def factors : Finset ℕ := {2,3,5,23,31}

private theorem data120 : ∀ a : Fin 120, a.val.Coprime 120 →
    ((fastUpper a.val).Coprime (fastF 120) ↔ a.val=41 ∨ a.val=89) ∧
    (a.val≠41 → a.val≠89 → ∃ p ∈ factors, p ∣ fastUpper a.val) := by decide +kernel

/-- Exactly two reduced classes modulo 120 escape all prime divisors of F₁₂₀. -/
theorem upper_period_120_coprime_iff (n : ℕ) (hu : n.Coprime 120) :
    (lucasFibonacciSum n).Coprime (Nat.fib 120) ↔ n%120=41 ∨ n%120=89 := by
  rw [Nat.coprime_iff_gcd_eq_one,upper_gcd_return]
  have h := (data120 ⟨n%120,Nat.mod_lt _ (by decide)⟩ (by simpa [Nat.Coprime] using hu)).1
  simpa [fastUpper_eq,fastF_eq,Nat.Coprime] using h

/-- Apart from 2 and 5, a prime index with prime upper value must be 41 or
89 modulo 120. Every excluded reduced class has a witness at most 31. -/
theorem upper_prime_value_at_prime_index {n : ℕ} (hn : n.Prime)
    (hU : (lucasFibonacciSum n).Prime) : n=2 ∨ n=5 ∨ n%120=41 ∨ n%120=89 := by
  by_cases h : n≤5
  · interval_cases n <;> first | decide | contradiction
  right; right
  by_contra! bad
  have hcop : n.Coprime 120 := hn.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have check : ∀ i : Fin 121, i.val.Prime → i.val ∣ 120 → i.val ≤ 5 := by decide
    exact h (check ⟨n, by have := Nat.le_of_dvd (by decide : 0<120) hdiv; omega⟩ hn hdiv))
  obtain ⟨p,hp,hd⟩ := (data120 ⟨n%120,Nat.mod_lt _ (by decide)⟩
    (by simpa [Nat.Coprime] using hcop)).2 bad.1 bad.2
  have checks : ∀ q ∈ factors, 1<q ∧ q≤31 ∧ q ∣ fastF 120 := by decide
  obtain ⟨hp1,hp31,hF⟩ := checks _ hp
  have hpn := (return_mod p 120 (by simpa [fastF_eq] using hF) n).mpr (by simpa [fastUpper_eq] using hd)
  have eq := (hU.eq_one_or_self_of_dvd _ hpn).resolve_left (by omega)
  have hmono : lucasFibonacciSum 6 ≤ lucasFibonacciSum n := by
    unfold lucasFibonacciSum
    gcongr <;> omega
  have h6 : lucasFibonacciSum 6=37 := by decide
  omega

#print axioms prime_indices_for_463_and_487
#print axioms upper_gcd_return
#print axioms upper_period_120_coprime_iff
#print axioms upper_prime_value_at_prime_index

end Arxiv.«2211.10788»
