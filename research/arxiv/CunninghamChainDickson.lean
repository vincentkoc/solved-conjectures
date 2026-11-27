import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import FormalConjectures.Paper.PrimeTuples

/-!
# Exact-length Cunningham chains from Dickson's conjecture

Lenny Jones, *Polynomial Cunningham Chains*, §1 (arXiv:1104.1579).
The chain predicate and the prime-tuples statement come from Formal Conjectures.
-/

namespace CunninghamChain

/-- Take the proposition from the upstream declaration. Its proof is an explicit hypothesis. -/
abbrev PrimeTuples : Prop := type_of% @PrimeTuplesConjecture.prime_tuples_conjecture

private theorem term_shift (x b i : ℕ) :
    firstKindTerm (x + b) i = 2 ^ i * x + firstKindTerm b i := by
  induction i with
  | zero => simp [firstKindTerm]
  | succ i ih => rw [firstKindTerm, firstKindTerm, ih, pow_succ]; ring

private theorem term_add_one (b i : ℕ) :
    firstKindTerm b i + 1 = 2 ^ i * (b + 1) := by
  induction i with
  | zero => simp [firstKindTerm]
  | succ i ih => rw [firstKindTerm, pow_succ]; nlinarith

private theorem term_strictMono (b : ℕ) : StrictMono (firstKindTerm b) :=
  strictMono_nat_of_lt_succ fun i => by simp only [firstKindTerm]; omega

/-- A prime dividing the seed plus one divides none of the terms. -/
private theorem not_dvd_term {p x : ℕ} (hp : p.Prime) (hx : p ∣ x + 1) (i : ℕ) :
    ¬p ∣ firstKindTerm x i := by
  intro h
  have hnext : p ∣ firstKindTerm x i + 1 := by
    rw [term_add_one]
    exact dvd_mul_of_dvd_right hx _
  exact hp.not_dvd_one ((Nat.dvd_add_right h).mp hnext)

/-- Apply Dickson to an admissible prefix along a progression. Repeating a form
keeps the hypothesis valid for a prefix of length one. -/
private theorem prime_prefixes (hD : PrimeTuples) {k q b : ℕ} (hk : 0 < k) (hq : 0 < q)
    (hadm : ∀ p, p.Prime → ∃ n, ∀ i < k, ¬p ∣ firstKindTerm (q * n + b) i) :
    Set.Infinite {n | ∀ i < k, (firstKindTerm (q * n + b) i).Prime} := by
  let idx (i : Fin (k + 1)) := i.val % k
  let a (i : Fin (k + 1)) : ℕ+ := ⟨2 ^ idx i * q, by positivity⟩
  let c (i : Fin (k + 1)) := firstKindTerm b (idx i)
  have hform (i : Fin (k + 1)) (n : ℕ) :
      a i * n + c i = firstKindTerm (q * n + b) (idx i) := by
    simp [a, c, term_shift, mul_assoc]
  apply (hD (by omega : 2 ≤ k + 1) a c ?_).mono
  · intro n hn i hi
    let j : Fin (k + 1) := ⟨i, by omega⟩
    simpa [hform, idx, j, Nat.mod_eq_of_lt hi] using hn j
  · intro p hp
    obtain ⟨n, hn⟩ := hadm p hp
    exact ⟨n, hp.prime.not_dvd_finsetProd fun i _ => by
      rw [hform]
      exact hn _ (Nat.mod_lt _ hk)⟩

/-- Assuming Dickson's prime-tuples conjecture, infinitely many primes begin a
first-kind Cunningham chain of each positive exact length. -/
theorem infinitely_many_firstKind_chains_of_primeTuples (hD : PrimeTuples) (k : ℕ) (hk : 0 < k) :
    Set.Infinite {p : ℕ | IsFirstKindChainOfLength p k} := by
  -- First obtain one prime prefix long enough to include the intended stopping term.
  have hprefix : Set.Infinite {b : ℕ | ∀ i < k + 1, (firstKindTerm (1 * b + 0) i).Prime} := by
    apply prime_prefixes hD (by omega) (by decide)
    intro p hp
    refine ⟨p - 1, fun i _ => not_dvd_term hp ?_ i⟩
    simp [Nat.sub_add_cancel hp.one_le]
  obtain ⟨b, hb⟩ := hprefix.nonempty
  change ∀ i < k + 1, (firstKindTerm (1 * b + 0) i).Prime at hb
  simp only [one_mul, add_zero] at hb
  let q := firstKindTerm b k
  have hq : q.Prime := hb k (by omega)
  -- Restrict the seed to b modulo q. Earlier terms stay locally admissible.
  have hprog : Set.Infinite {n : ℕ | ∀ i < k, (firstKindTerm (q * n + b) i).Prime} := by
    apply prime_prefixes hD hk hq.pos
    intro p hp
    by_cases heq : p = q
    · subst p
      refine ⟨0, fun i hi => ?_⟩
      simpa using Nat.not_dvd_of_pos_of_lt (hb i (by omega)).pos (term_strictMono b hi)
    · let : Fact p.Prime := ⟨hp⟩
      have hunit : (q : ZMod p) ≠ 0 := by
        rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq hp hq]
      obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective
        ((-((b : ZMod p) + 1)) / (q : ZMod p))
      refine ⟨n, fun i _ => not_dvd_term hp ?_ i⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [hn]
      field_simp
      ring
  rw [Set.infinite_iff_exists_gt]
  intro bound
  obtain ⟨n, hn, hlarge⟩ := Set.infinite_iff_exists_gt.mp hprog bound
  have hstop : firstKindTerm (q * n + b) k = q * (2 ^ k * n + 1) := by
    rw [term_shift]
    change 2 ^ k * (q * n) + q = _
    ring
  refine ⟨q * n + b, ⟨hk, hn, ?_⟩, ?_⟩
  · rw [hstop]
    have hpos : 0 < 2 ^ k * n := Nat.mul_pos (by positivity) (by omega)
    exact Nat.not_prime_mul hq.ne_one (by omega)
  · have := Nat.le_mul_of_pos_left n hq.pos
    omega

end CunninghamChain

#print axioms CunninghamChain.infinitely_many_firstKind_chains_of_primeTuples
