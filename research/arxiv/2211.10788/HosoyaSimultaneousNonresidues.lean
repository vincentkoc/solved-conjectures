import Mathlib

/-! Quadratic reciprocity and prime moduli that exclude both Pell discriminants. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Finset

private lemma nonsquare_residue (q : ℕ) (hp : q.Prime) (ho : q≠2) :
    ∃ c : ℕ, c.Coprime q ∧ ¬IsSquare (c : ZMod q) := by
  let : Fact q.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  have hn : x≠0 := by rintro rfl; exact hx IsSquare.zero
  refine ⟨x.val, (hp.coprime_iff_not_dvd.mpr ?_).symm, by simpa using hx⟩
  intro h
  exact hn (by simpa using (ZMod.natCast_eq_zero_iff ..).mpr h)

/-- Eight times the product of the odd primes of S when S consists of primes. -/
def signModulus (S : Finset ℕ) := ∏ q ∈ insert 2 S, q^(if q=2 then 3 else 1)

/-- Prescribe the Legendre signs of any finite set of primes on one reduced prime progression. -/
theorem prescribe_prime_signs (S T : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∃ M r : ℕ, M=signModulus S ∧ 0<M ∧ r.Coprime M ∧
      ∀ p (hp : p.Prime), p ≡ r [MOD M] → p%4=1 ∧ ∀ q ∈ S,
        @legendreSym p ⟨hp⟩ q = if q∈T then -1 else 1 := by
  classical
  let U := insert 2 S
  let e (q : ℕ) : ℕ := if q=2 then 3 else 1
  let m (q : ℕ) := q^(e q)
  let c (q : ℕ) : ℕ := if q=2 then (if 2∈T then 5 else 1)
    else if h : q.Prime ∧ q≠2 ∧ q∈T then (nonsquare_residue q h.1 h.2.1).choose else 1
  have pu (q : ℕ) (hq : q∈U) : q.Prime := by
    rcases mem_insert.mp hq with rfl | h
    · exact Nat.prime_two
    · exact hS _ h
  have cop (q : ℕ) (hq : q∈U) : (c q).Coprime (m q) := by
    by_cases h2 : q=2
    · subst q
      by_cases hT : 2∈T <;> simp [m,e,c,hT]
      decide
    · have hpr := pu q hq
      by_cases hT : q∈T
      · simpa [m,e,c,h2,hT,hpr] using (nonsquare_residue q hpr h2).choose_spec.1
      · simp [m,e,c,h2,hT]
  have hn (q : ℕ) (hq : q∈U) : m q ≠ 0 := pow_ne_zero _ (pu q hq).ne_zero
  have co : Set.Pairwise (U : Set ℕ) (fun q v => (m q).Coprime (m v)) :=
    fun q hq v hv h => Nat.coprime_pow_primes _ _ (pu q hq) (pu v hv) h
  let M := ∏ q ∈ U, m q
  let r := Nat.chineseRemainderOfFinset c m U hn co
  refine ⟨M,r,rfl,Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr hn),Nat.Coprime.prod_right ?_,?_⟩
  · intro q hq
    exact ((r.property q hq).gcd_eq.trans (cop q hq))
  intro p hp hM
  let : Fact p.Prime := ⟨hp⟩
  have loc (v : ℕ) (hv : v∈U) : p ≡ c v [MOD m v] :=
    (hM.of_dvd (Finset.dvd_prod_of_mem m hv)).trans (r.property v hv)
  have h8 : p ≡ (if 2∈T then 5 else 1) [MOD 8] := by
    simpa [e,m,c] using loc 2 (mem_insert_self _ _)
  have h4 : p%4=1 := by
    have h := h8.of_dvd (by decide : 4∣8)
    split at h <;> exact h
  refine ⟨h4,?_⟩
  intro q hq
  have hp2 : p≠2 := by omega
  by_cases h2 : q=2
  · subst q
    rw [show ((2:ℕ):ℤ)=2 by decide, legendreSym.at_two hp2]
    have hx := (ZMod.natCast_eq_natCast_iff ..).mpr h8
    by_cases hT : 2∈T
    · rw [if_pos hT] at hx ⊢
      rw [hx]; decide
    · rw [if_neg hT] at hx ⊢
      rw [hx]; decide
  have hpr := hS q hq
  let : Fact q.Prime := ⟨hpr⟩
  rw [←legendreSym.quadratic_reciprocity_one_mod_four h4 h2]
  have he : (p:ZMod q)=c q := (ZMod.natCast_eq_natCast_iff ..).mpr
    (by simpa [m,e,h2] using loc q (mem_insert_of_mem hq))
  by_cases hT : q∈T
  · rw [if_pos hT, legendreSym.eq_neg_one_iff',he]
    simpa [c,hpr,h2,hT] using (nonsquare_residue q hpr h2).choose_spec.2
  · have hp1 : (p:ZMod q)=1 := by simpa [c,h2,hT] using he
    rw [if_neg hT]
    simp [legendreSym,hp1]

private lemma odd_factor {N : ℕ} (hN : ¬IsSquare N) :
    ∃ q ∈ N.primeFactors, Odd (N.factorization q) := by
  have hn : N≠0 := by rintro rfl; exact hN IsSquare.zero
  by_contra! h
  apply hN
  rw [Nat.prod_primeFactors_pow_factorization hn]
  apply Finset.isSquare_prod
  intro q hq
  have he := Nat.not_odd_iff_even.mp (h q hq)
  obtain ⟨a,ha⟩ := he
  exact ⟨q^a,by rw [ha,pow_add]⟩

private lemma negative_of_one_odd {p N u : ℕ} [Fact p.Prime] (hn : N≠0)
    (hu : u∈N.primeFactors) (huo : Odd (N.factorization u)) (hs : legendreSym p u = -1)
    (hother : ∀ q ∈ N.primeFactors, q≠u → legendreSym p q=1 ∨ Even (N.factorization q))
    (hnz : ∀ q ∈ N.primeFactors, legendreSym p q=1 ∨ legendreSym p q= -1) :
    ¬ IsSquare (N : ZMod p) := by
  apply (legendreSym.eq_neg_one_iff' p).mp
  have whole : legendreSym p N = ∏ q ∈ N.primeFactors, (legendreSym p q)^(N.factorization q) := by
    change legendreSym.hom p (N:ℤ) = _
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    simp only [Nat.cast_prod,Nat.cast_pow,map_prod,map_pow,legendreSym.hom_apply]
  rw [whole,Finset.prod_eq_single_of_mem u hu,hs,huo.neg_one_pow]
  intro q hq hqu
  rcases hother q hq hqu with h | h
  · simp [h]
  · rcases hnz q hq with he|he
    · simp [he]
    · rw [he,h.neg_one_pow]

/-- Every two positive nonsquares are both nonsquares at all primes in one reduced class. -/
theorem two_nonsquares_prime_progression {A B : ℕ} (hA : ¬IsSquare A) (hB : ¬IsSquare B) :
    ∃ M r : ℕ, M=signModulus (A.primeFactors ∪ B.primeFactors) ∧ 0<M ∧ r.Coprime M ∧
      ∀ p : ℕ, p.Prime → p ≡ r [MOD M] → p%4=1 ∧ ¬IsSquare (A : ZMod p) ∧ ¬IsSquare (B : ZMod p) := by
  classical
  let S := A.primeFactors ∪ B.primeFactors
  have hS : ∀ q ∈ S, q.Prime := by
    intro q hq
    rcases mem_union.mp hq with h|h <;> exact Nat.prime_of_mem_primeFactors h
  have nonzero {N : ℕ} (hn : ¬IsSquare N) : N≠0 := by rintro rfl; exact hn IsSquare.zero
  obtain ⟨u,hu,huo⟩ := odd_factor hA
  obtain ⟨v,hv,hvo⟩ := odd_factor hB
  have select : ∃ T : Finset ℕ, (∃ i ∈ A.primeFactors, i∈T ∧ Odd (A.factorization i) ∧
      ∀ q∈A.primeFactors, q∈T → q≠i → Even (A.factorization q)) ∧
      (∃ j ∈ B.primeFactors, j∈T ∧ Odd (B.factorization j) ∧
      ∀ q∈B.primeFactors, q∈T → q≠j → Even (B.factorization q)) := by
    by_cases hc : ∃ q, Odd (A.factorization q) ∧ Odd (B.factorization q)
    · obtain ⟨q,h₁,h₂⟩ := hc
      have mem {N : ℕ} (ho : Odd (N.factorization q)) : q∈N.primeFactors := by
        rw [←Nat.support_factorization,Finsupp.mem_support_iff]
        rintro hh; simp [hh] at ho
      have only {N v : ℕ} (hv : v∈({q}:Finset ℕ)) (hne : v≠q) : Even (N.factorization v) :=
        (hne (Finset.mem_singleton.mp hv)).elim
      exact ⟨{q},⟨q,mem h₁,by simp,h₁,fun _ _ => only⟩,⟨q,mem h₂,by simp,h₂,fun _ _ => only⟩⟩
    · refine ⟨{u,v},⟨u,hu,by simp,huo,?_⟩,⟨v,hv,by simp,hvo,?_⟩⟩
      · intro q _ hq hqu
        have eq : q=v := by simpa [hqu] using hq
        subst q
        exact Nat.not_odd_iff_even.mp (fun ho => hc ⟨v,ho,hvo⟩)
      · intro q _ hq hqv
        have eq : q=u := by simpa [hqv] using hq
        subst q
        exact Nat.not_odd_iff_even.mp (fun ho => hc ⟨u,huo,ho⟩)
  obtain ⟨T,h₁,h₂⟩ := select
  obtain ⟨M,r,hmEq,hM,hr,signs⟩ := prescribe_prime_signs S T hS
  refine ⟨M,r,hmEq,hM,hr,?_⟩
  intro p hp he
  obtain ⟨h4,signs⟩ := signs p hp he
  let : Fact p.Prime := ⟨hp⟩
  have applyOne {N : ℕ} (hn : ¬IsSquare N) (hsub : N.primeFactors⊆S)
      (hh : ∃ i ∈ N.primeFactors, i∈T ∧ Odd (N.factorization i) ∧
          ∀ q∈N.primeFactors, q∈T → q≠i → Even (N.factorization q)) :
      ¬IsSquare (N:ZMod p) := by
    obtain ⟨i,hi,hit,hio,hrest⟩ := hh
    refine negative_of_one_odd (nonzero hn) hi hio (by simpa [hit] using signs i (hsub hi)) ?_ ?_
    · intro q hq hqi
      by_cases hqt : q∈T
      · exact Or.inr (hrest q hq hqt hqi)
      · exact Or.inl (by simpa [hqt] using signs q (hsub hq))
    · intro q hq
      rw [signs q (hsub hq)]
      split <;> simp
  exact ⟨h4,applyOne hA Finset.subset_union_left h₁,applyOne hB Finset.subset_union_right h₂⟩

#print axioms prescribe_prime_signs
#print axioms two_nonsquares_prime_progression

end Arxiv.«2211.10788».PrimeObstruction
