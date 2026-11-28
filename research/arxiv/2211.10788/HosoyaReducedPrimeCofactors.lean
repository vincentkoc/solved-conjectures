import HosoyaPrimeIndexSieve

/-! Freezing all small prime factors along a reduced prime-index progression. -/

namespace Arxiv.«2211.10788»

private lemma term_pos (n : ℕ) : 0 < lucasFibonacciSum n := by
  have := Nat.fib_pos.mpr (by omega : 0<n+2)
  unfold lucasFibonacciSum
  omega

private lemma rank_spec₁ (m : ℕ) [NeZero m] :
    0<fibonacciStepRank m 1 ∧ m ∣ Nat.fib (fibonacciStepRank m 1) := by
  have h : 0 < fibonacciStepRank m 1 ∧ m ∣ Nat.fib (1 * fibonacciStepRank m 1) := by
    unfold fibonacciStepRank
    exact Nat.find_spec (p := fun t => 0 < t ∧ m ∣ Nat.fib (1*t)) _
  simpa only [one_mul] using h

private def rankPow (p k : ℕ) (hp : p.Prime) : ℕ :=
  let _ : NeZero p := ⟨hp.ne_zero⟩
  fibonacciStepRank (p^(k+1)) 1

private lemma rankPow_spec (p k : ℕ) (hp : p.Prime) :
    0<rankPow p k hp ∧ p^(k+1) ∣ Nat.fib (rankPow p k hp) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  exact rank_spec₁ _

private lemma rankPow_coprime {p s : ℕ} (hp : p.Prime) (hs : s.Coprime p)
    (he : s.Coprime (rankPow p 0 hp)) (k : ℕ) : s.Coprime (rankPow p k hp) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  induction k with
  | zero => exact he
  | succ k ih =>
    have eq : rankPow p (k+1) hp = fibonacciStepRank (p*p^(k+1)) 1 := by
      unfold rankPow
      congr 1
      · exact pow_succ' p (k+1)
      · exact proof_irrel_heq ..
    rw [eq,fibonacciStepRank_prime_mul (dvd_pow_self p (by omega : k+1≠0)) 1]
    split
    · exact ih
    · exact hs.mul_right ih

/-- Inside every reduced index class and beyond any bound, one can fix a
divisor A of an anchor term and make the quotient coprime to each prime in
a prescribed finite set on an entire reduced refinement. -/
theorem upper_prime_index_fixed_cofactor (S : Finset ℕ) (hp : ∀ p ∈ S, Nat.Prime p)
    {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m) (B : ℕ) :
    ∃ s L A : ℕ, B<s ∧ s.Prime ∧ s ≡ a [MOD m] ∧
      0<L ∧ m ∣ L ∧ s.Coprime L ∧ A ∣ lucasFibonacciSum s ∧
      ∀ t, t ≡ s [MOD L] → ∃ C, lucasFibonacciSum t=A*C ∧ ∀ p ∈ S, ¬p ∣ C := by
  classical
  let base (i : S) := i.val*rankPow i.val 0 (hp i.val i.prop)
  let E := ∏ i : S, base i
  have hE : 0<E := Finset.prod_pos fun i _ => Nat.mul_pos (hp i.val i.prop).pos
    (rankPow_spec i.val 0 (hp i.val i.prop)).1
  obtain ⟨s,hB,hs,hsm⟩ := Nat.forall_exists_prime_gt_and_modEq (max B E) hm.ne' ha
  have hsE : s.Coprime E := hs.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hE (by omega))
  let h (i : S) := (lucasFibonacciSum s).factorization i.val
  let e (i : S) := rankPow i.val (h i) (hp i.val i.prop)
  let L := m * ∏ i : S, e i
  have pos : 0<L := Nat.mul_pos hm (Finset.prod_pos fun i _ => (rankPow_spec ..).1)
  have unit : s.Coprime L := by
    apply ((show s.Coprime m from (show s.gcd m=a.gcd m from hsm.gcd_eq).trans ha)).mul_right
    apply Nat.coprime_prod_right_iff.mpr
    intro i _
    have bd : base i ∣ E := Finset.dvd_prod_of_mem base (Finset.mem_univ i)
    have cp := hsE.of_dvd_right bd
    exact rankPow_coprime (hp i.val i.prop) (cp.of_dvd_right (dvd_mul_right ..))
      (cp.of_dvd_right (dvd_mul_left ..)) _
  let A := (lucasFibonacciSum s).gcd (Nat.fib L)
  have hAs : A ∣ lucasFibonacciSum s := Nat.gcd_dvd_left ..
  have hA := Nat.pos_of_dvd_of_pos hAs (term_pos s)
  refine ⟨s,L,A,by omega,hs,hsm,pos,dvd_mul_right ..,unit,hAs,?_⟩
  intro t ht
  have g : (lucasFibonacciSum t).gcd (Nat.fib L)=A := by
    rw [upper_gcd_return,show t%L=s%L from ht,←upper_gcd_return]
  obtain ⟨C,hu⟩ := g ▸ (Nat.gcd_dvd_left (lucasFibonacciSum t) (Nat.fib L))
  refine ⟨C,hu,?_⟩
  intro p hmem hC
  let i : S := ⟨p,hmem⟩
  have hd : e i ∣ L := (Finset.dvd_prod_of_mem e (Finset.mem_univ i)).trans (dvd_mul_left ..)
  have powF := (rankPow_spec p (h i) (hp p hmem)).2.trans (Nat.fib_dvd _ _ hd)
  have nz := (Nat.fib_pos.mpr pos).ne'
  have gt := ((hp p hmem).pow_dvd_iff_le_factorization nz).mp powF
  have low := (Nat.factorization_le_iff_dvd hA.ne' (term_pos s).ne').mpr hAs p
  have heq := congrArg (fun z : ℕ => z.factorization p) g
  rw [Nat.factorization_gcd (term_pos t).ne' nz] at heq
  change min ((lucasFibonacciSum t).factorization p) ((Nat.fib L).factorization p) = A.factorization p at heq
  change (lucasFibonacciSum s).factorization p+1 ≤ (Nat.fib L).factorization p at gt
  have hc : C≠0 := by intro hh; have := term_pos t; simp [hh] at hu; omega
  rw [hu,Nat.factorization_mul hA.ne' hc,Finsupp.add_apply] at heq
  have hv := (hp p hmem).factorization_pos_of_dvd hc hC
  omega

#print axioms upper_prime_index_fixed_cofactor

end Arxiv.«2211.10788»
