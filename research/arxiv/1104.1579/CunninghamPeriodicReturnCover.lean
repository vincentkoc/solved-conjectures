import CunninghamReturnCoverPrimes
import research.arxiv.«1104.1579».CunninghamSquarefreePrimeSeeds

/-! # Periodic confinement of Cunningham prime returns -/

namespace CunninghamChain.ReturnCover
open Finset

/-- A finite set of local obstructions for which the surviving exponents are
exactly the multiples of a period. The exponent zero survives at every prime. -/
structure PeriodCover (D : ℕ) where
  Index : Type
  finiteIndex : Fintype Index
  primeAt : Index → ℕ
  distinct : Function.Injective primeAt
  prime : ∀ i, (primeAt i).Prime
  oddPrime : ∀ i, 2<primeAt i
  site : Index → ℕ
  survives : ∀ j : ℕ, (∀ i, (2:ZMod (primeAt i))^j ≠ (2:ZMod (primeAt i))^(site i)) ↔ D ∣ j

private theorem cover_with_odd_part {m L : ℕ} (hm : Odd m) :
    ∃ B : ℕ, L≤B ∧ Nonempty (PeriodCover (2^B*m)) := by
  classical
  have hp : ∃ B : ℕ, L≤B ∧ ∃ g : ℕ → ℕ, (∀ i < m-1, (g i).Prime ∧ 2<g i ∧
      orderOf ((2:ZMod (g i))^(2^B))=m) ∧ Set.InjOn g (Set.Iio (m-1)) := by
    by_cases hmany : 1 < m
    · exact simultaneous_order_primes hm hmany L (m-1)
    · refine ⟨L,le_rfl,fun _ => 0,?_,?_⟩
      · intro i hi; omega
      · intro i hi; change i < m-1 at hi; omega
  obtain ⟨B,hB,g,hg,hgi⟩ := hp
  obtain ⟨f,hfi,hf,hfcover⟩ := fermat_cover
  let I := Fin B ⊕ Fin (m-1)
  let q : I → ℕ := Sum.elim (fun i => f i.val) (fun i => g i.val)
  let site : I → ℕ := Sum.elim (fun i => 2^i.val) (fun i => 2^B*(i.val+1))
  have disj (i : Fin B) (j : Fin (m-1)) : f i.val≠g j.val := by
    intro he
    have h := fermat_power_later i.isLt (hf i).2.2
    rw [he] at h
    have hh := (hg j j.isLt).2.2
    rw [h,orderOf_one] at hh
    have := j.isLt
    omega
  refine ⟨B,hB,⟨⟨I,inferInstance,q,?_,?_,?_,site,?_⟩⟩⟩
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Fin.ext (hfi hij))
      | inr j => exact (disj i j hij).elim
    | inr i =>
      cases j with
      | inl j => exact (disj j i hij.symm).elim
      | inr j => exact congrArg Sum.inr (Fin.ext (hgi i.isLt j.isLt hij))
  · rintro (i|i)
    · exact (hf i).1
    · exact (hg i i.isLt).1
  · rintro (i|i)
    · exact (hf i).2.1
    · exact (hg i i.isLt).2.1
  · intro j
    constructor
    · intro hh
      have hd : 2^B ∣ j := (hfcover B j).mp (by
        intro i hi hit
        exact hh (.inl ⟨i,hi⟩) (hit.trans (hf i).2.2.symm))
      obtain ⟨k,rfl⟩ := hd
      suffices h : m ∣ k by exact Nat.mul_dvd_mul_left _ h
      by_contra hbad
      have ho := hm.pos
      have hpos : 0<k%m := Nat.pos_of_ne_zero (fun h => hbad (Nat.dvd_of_mod_eq_zero h))
      have hlt := Nat.mod_lt k ho
      let i : Fin (m-1) := ⟨k%m-1,by omega⟩
      have he := hh (.inr i)
      change (2:ZMod (g i))^(2^B*k) ≠ (2:ZMod (g i))^(2^B*(i.val+1)) at he
      apply he
      rw [pow_mul,pow_mul,show i.val+1=k%m by dsimp [i]; omega]
      let x := (2:ZMod (g i))^(2^B)
      exact (pow_mod_orderOf x k).symm.trans (congrArg (fun t : ℕ => x^(k%t)) (hg i i.isLt).2.2)
    · rintro ⟨k,rfl⟩ (i|i)
      · change (2:ZMod (f i))^(2^B*m*k)≠(2:ZMod (f i))^(2^i.val)
        intro hit
        exact (hfcover B _).mpr (by exact ⟨m*k,mul_assoc ..⟩) i i.isLt (hit.trans (hf i).2.2)
      · let x := (2:ZMod (g i))^(2^B)
        have hx : orderOf x=m := (hg i i.isLt).2.2
        change (2:ZMod (g i))^(2^B*m*k) ≠ (2:ZMod (g i))^(2^B*(i.val+1))
        rw [mul_assoc,pow_mul (2:ZMod (g i)) (2^B) (m*k),pow_mul (2:ZMod (g i)) (2^B) (i.val+1)]
        change x^(m*k)≠x^(i.val+1)
        have hxpow : x^m=1 := (congrArg (fun t : ℕ => x^t) hx).symm.trans (pow_orderOf_eq_one x)
        rw [pow_mul,hxpow,one_pow]
        intro he
        have hd := orderOf_dvd_of_pow_eq_one he.symm
        rw [hx] at hd
        have := Nat.le_of_dvd (Nat.succ_pos _) hd
        have := i.isLt
        omega

/-- Each requested positive modulus divides an exact period of a finite cover. -/
theorem exists_period_cover (M : ℕ) (hM : 0<M) :
    ∃ D : ℕ, 0<D ∧ M ∣ D ∧ Nonempty (PeriodCover D) := by
  obtain ⟨L,m,hm,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hM.ne'
  obtain ⟨B,hB,hcover⟩ := cover_with_odd_part (L:=L) hm
  exact ⟨_,Nat.mul_pos (by positivity) hm.pos,Nat.mul_dvd_mul (pow_dvd_pow 2 hB) dvd_rfl,hcover⟩

open SquarefreeSeeds in
private theorem root_congruence (first : Bool) {q : ℕ} [Fact q.Prime] (i j : ℕ) :
    root first q i ≡ root first q j [MOD q] ↔ (2:ZMod q)^i=(2:ZMod q)^j := by
  rw [←ZMod.natCast_eq_natCast_iff]
  cases first <;> simp [root,fixed]

/-- Both recurrences admit reduced seed classes with exactly the same periodic
set of indices free of the covering primes. Every positive modulus divides
one such period. -/
theorem periodic_seed_classes (M : ℕ) (hM : 0<M) :
    ∃ D W : ℕ, 0<D ∧ M ∣ D ∧ 0<W ∧ ∀ first : Bool, ∃ A : ℕ, A.Coprime W ∧
      ∀ p : ℕ, 0<p → p ≡ A [MOD W] → ∀ j : ℕ,
        (SquarefreeSeeds.term first p j).Coprime W ↔ D ∣ j := by
  classical
  obtain ⟨D,hD,hMD,⟨c⟩⟩ := exists_period_cover M hM
  let : Fintype c.Index := c.finiteIndex
  let q := c.primeAt
  let W := ∏ i, q i
  have hq (i) : (q i).Prime := c.prime i
  have hW : 0<W := prod_pos (fun i _ => (hq i).pos)
  refine ⟨D,W,hD,hMD,hW,?_⟩
  intro first
  let r i := SquarefreeSeeds.root first (q i) (c.site i)
  obtain ⟨A,hA⟩ := Nat.chineseRemainderOfFinset r q univ (fun i _ => (hq i).ne_zero)
    (fun i _ j _ h => (Nat.coprime_primes (hq i) (hq j)).mpr (c.distinct.ne h))
  have r_unit (i) : (r i).Coprime (q i) := by
    let : Fact (q i).Prime := ⟨hq i⟩
    apply Nat.Coprime.symm
    apply (hq i).coprime_iff_not_dvd.mpr
    intro h
    have he : SquarefreeSeeds.root first (q i) 0 ≡ r i [MOD q i] := by
      have hz := Nat.modEq_zero_iff_dvd.mpr h
      simpa [SquarefreeSeeds.root] using hz.symm
    exact ((c.survives 0).mpr (dvd_zero D) i) ((root_congruence first 0 (c.site i)).mp he)
  refine ⟨A,Nat.Coprime.prod_right fun i hi => (hA i hi).gcd_eq.trans (r_unit i),?_⟩
  intro p hp hclass j
  rw [←c.survives j]
  change (SquarefreeSeeds.term first p j).Coprime (∏ i,q i) ↔ _
  rw [Nat.coprime_prod_right_iff]
  simp only [mem_univ,true_implies]
  apply forall_congr'
  intro i
  let : Fact (q i).Prime := ⟨hq i⟩
  have hodd := (Nat.coprime_primes Nat.prime_two (hq i)).mpr (c.oddPrime i).ne
  have hpi := (hclass.of_dvd (dvd_prod_of_mem q (mem_univ i))).trans (hA i (mem_univ i))
  rw [Nat.coprime_comm,(hq i).coprime_iff_not_dvd,SquarefreeSeeds.root_iff first hp hodd j]
  apply not_congr
  refine ⟨fun h => (root_congruence first j _).mp (h.symm.trans hpi),
    fun h => hpi.trans ((root_congruence first j _).mpr h).symm⟩

private theorem seed_le_site (first : Bool) {p : ℕ} (_hp : 0<p) (j : ℕ) :
    p≤SquarefreeSeeds.term first p j := by
  induction j with
  | zero => cases first <;> simp [SquarefreeSeeds.term,firstKindTerm,secondKindTerm]
  | succ j ih =>
    cases first <;> simp only [SquarefreeSeeds.term,Bool.false_eq_true,if_false,if_true,
      firstKindTerm,secondKindTerm] at ih ⊢ <;> omega

/-- Infinitely many prime seeds have every future prime return confined to
multiples of any prescribed positive modulus, for each canonical recurrence. -/
theorem infinitely_many_confined_prime_returns (M : ℕ) (hM : 0<M) (first : Bool) :
    {p : ℕ | p.Prime ∧ ∀ j : ℕ, ((if first then firstKindTerm else secondKindTerm) p j).Prime →
      M ∣ j}.Infinite := by
  obtain ⟨D,W,_,hMD,hW,h⟩ := periodic_seed_classes M hM
  obtain ⟨A,hu,hA⟩ := h first
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p,hp,hprime,hr⟩ := Nat.forall_exists_prime_gt_and_modEq (N+W) hW.ne' hu
  refine ⟨p,⟨hprime,?_⟩,by omega⟩
  intro j hj
  change (SquarefreeSeeds.term first p j).Prime at hj
  have hlt := seed_le_site first hprime.pos j
  have hcop := hj.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hW (by omega))
  exact hMD.trans ((hA p hprime.pos hr j).mp hcop)

#print axioms periodic_seed_classes
#print axioms infinitely_many_confined_prime_returns

#print axioms exists_period_cover

end CunninghamChain.ReturnCover
