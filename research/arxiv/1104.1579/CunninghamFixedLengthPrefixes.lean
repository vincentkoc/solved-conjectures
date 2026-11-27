import CunninghamUnboundedPrefixes
import FormalConjectures.Wikipedia.Dickson

/-! Infinite prime prefixes of a fixed length suffice for infinitely many exact
chains of that same length. Prime-to-prime steps may also preserve a seed set. -/

namespace CunninghamChain

/-- Follow a finite orbit to a suffix of the requested exact length. The seed
may move, so preserve membership only on steps whose endpoints are prime. -/
private theorem fixed_length_in_set (t : ℕ → ℕ → ℕ) (f : ℕ → ℕ)
    (start : ∀ p, t p 0 = p) (shift : ∀ p i, t (f p) i = t p (i + 1))
    (grow : ∀ p, p.Prime → p ≤ f p)
    (stops : ∀ p, p.Prime → ∃ i, ¬(t p i).Prime)
    (k : ℕ) (hk : 0 < k) (S : Set ℕ)
    (closed : ∀ p ∈ S, p.Prime → (f p).Prime → f p ∈ S) :
    {p : ℕ | p ∈ S ∧ (0 < k ∧ (∀ i < k, (t p i).Prime) ∧ ¬(t p k).Prime)}.Infinite ↔
      {p : ℕ | p ∈ S ∧ ∀ i < k, (t p i).Prime}.Infinite := by
  constructor
  · intro h
    exact h.mono fun p hp => ⟨hp.1, hp.2.2.1⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro B
    obtain ⟨p, ⟨hS, hpre⟩, hB⟩ := h.exists_gt B
    obtain ⟨N, hN⟩ := stops p (start p ▸ hpre 0 hk)
    induction N generalizing p with
    | zero => exact (hN (hpre 0 hk)).elim
    | succ N ih =>
      by_cases hend : (t p k).Prime
      · have hpre' (i : ℕ) (hi : i < k) : (t (f p) i).Prime := by
          rw [shift]
          rcases lt_or_eq_of_le (show i + 1 ≤ k by omega) with hlt | heq
          · exact hpre _ hlt
          · simpa only [heq] using hend
        have hp : p.Prime := start p ▸ hpre 0 hk
        have hf : (f p).Prime := start (f p) ▸ hpre' 0 hk
        exact ih (f p) (hB.trans_le (grow p hp)) (closed p hS hp hf) hpre' (by rwa [shift])
      · exact ⟨p, ⟨hS, hk, hpre, hend⟩, hB⟩

/-- Fixed-length equivalence for any first-kind seed set closed on prime edges. -/
theorem firstKind_fixed_length_in_set (k : ℕ) (hk : 0 < k) (S : Set ℕ)
    (closed : ∀ p ∈ S, p.Prime → (2 * p + 1).Prime → 2 * p + 1 ∈ S) :
    {p : ℕ | p ∈ S ∧ IsFirstKindChainOfLength p k}.Infinite ↔
      {p : ℕ | p ∈ S ∧ ∀ i < k, (firstKindTerm p i).Prime}.Infinite := by
  apply fixed_length_in_set firstKindTerm (fun p => 2 * p + 1) (fun _ => rfl) _ (by omega) _ k hk S closed
  · intro p i
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun n : ℕ => 2 * n + 1) ih
  · intro p hp
    by_cases he : p = 2
    · subst p; exact ⟨5, two_starts_firstKind_length_five.2.2⟩
    · exact ⟨p - 1, (both_nonprime_at_pred_of_odd_prime hp he).1⟩

/-- Fixed-length equivalence for any second-kind seed set closed on prime edges. -/
theorem secondKind_fixed_length_in_set (k : ℕ) (hk : 0 < k) (S : Set ℕ)
    (closed : ∀ p ∈ S, p.Prime → (2 * p - 1).Prime → 2 * p - 1 ∈ S) :
    {p : ℕ | p ∈ S ∧ IsSecondKindChainOfLength p k}.Infinite ↔
      {p : ℕ | p ∈ S ∧ ∀ i < k, (secondKindTerm p i).Prime}.Infinite := by
  apply fixed_length_in_set secondKindTerm (fun p => 2 * p - 1) (fun _ => rfl) _ (by omega) _ k hk S closed
  · intro p i
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun n : ℕ => 2 * n - 1) ih
  · intro p hp
    by_cases he : p = 2
    · subst p; exact ⟨3, by decide⟩
    · exact ⟨p - 1, (both_nonprime_at_pred_of_odd_prime hp he).2⟩

theorem firstKind_fixed_length_iff_prime_prefixes (k : ℕ) (hk : 0 < k) :
    {p : ℕ | IsFirstKindChainOfLength p k}.Infinite ↔
      {p : ℕ | ∀ i < k, (firstKindTerm p i).Prime}.Infinite := by
  simpa using firstKind_fixed_length_in_set k hk Set.univ (by simp)

theorem secondKind_fixed_length_iff_prime_prefixes (k : ℕ) (hk : 0 < k) :
    {p : ℕ | IsSecondKindChainOfLength p k}.Infinite ↔
      {p : ℕ | ∀ i < k, (secondKindTerm p i).Prime}.Infinite := by
  simpa using secondKind_fixed_length_in_set k hk Set.univ (by simp)

/-- In the classes −1 (first kind) and 1 (second kind) modulo any positive
modulus, passing to an exact suffix preserves the divisibility condition. -/
theorem fixed_length_in_divisibility_classes (d k : ℕ) (hk : 0 < k) :
    ({p : ℕ | d ∣ p + 1 ∧ IsFirstKindChainOfLength p k}.Infinite ↔
      {p : ℕ | d ∣ p + 1 ∧ ∀ i < k, (firstKindTerm p i).Prime}.Infinite) ∧
    ({p : ℕ | d ∣ p - 1 ∧ IsSecondKindChainOfLength p k}.Infinite ↔
      {p : ℕ | d ∣ p - 1 ∧ ∀ i < k, (secondKindTerm p i).Prime}.Infinite) := by
  constructor
  · apply firstKind_fixed_length_in_set k hk {p | d ∣ p + 1}
    intro p h _ _
    change d ∣ p + 1 at h
    change d ∣ 2 * p + 1 + 1
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using (dvd_mul_of_dvd_right h 2)
  · apply secondKind_fixed_length_in_set k hk {p | d ∣ p - 1}
    intro p h _ _
    change d ∣ p - 1 at h
    change d ∣ 2 * p - 1 - 1
    rw [show 2 * p - 1 - 1 = 2 * (p - 1) by omega]
    exact dvd_mul_of_dvd_right h 2

/-- The length-two instance of Jones's first-kind conjecture is equivalent to
the pinned Sophie Germain prime conjecture, including the exact stopping term. -/
theorem firstKind_exact_two_iff_safe_primes :
    {p : ℕ | IsFirstKindChainOfLength p 2}.Infinite ↔ (type_of% Dickson.infinite_safe_primes) := by
  rw [firstKind_fixed_length_iff_prime_prefixes 2 (by decide)]
  rw [Set.infinite_coe_iff]
  have hs : {p : ℕ | ∀ i < 2, (firstKindTerm p i).Prime} =
      {p : ℕ | Prime p ∧ Prime (2 * p + 1)} := by
    ext p
    simp only [Set.mem_ofPred_eq, ← Nat.prime_iff]
    constructor
    · intro h; exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · rintro ⟨hp, hq⟩ i hi
      interval_cases i
      · exact hp
      · exact hq
  rw [hs]

#print axioms firstKind_fixed_length_in_set
#print axioms secondKind_fixed_length_in_set
#print axioms firstKind_fixed_length_iff_prime_prefixes
#print axioms secondKind_fixed_length_iff_prime_prefixes
#print axioms fixed_length_in_divisibility_classes
#print axioms firstKind_exact_two_iff_safe_primes

end CunninghamChain
