import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

/-! Jones's exact-length infinitude conjectures are equivalent to unbounded prime
prefix lengths, separately for the two kinds. -/

namespace CunninghamChain

/-- In an odd prime seed's orbit, Fermat's little theorem makes the term at index
p − 1 a multiple of p for either sign of the affine recurrence. -/
private theorem composite_at_pred {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : ℕ → ℕ)
    (hstart : t 0 = p) (hg : StrictMono t) (c : ZMod p)
    (hstep : ∀ i, (t (i + 1) : ZMod p) = 2 * t i + c) : ¬ (t (p - 1)).Prime := by
  let : Fact p.Prime := ⟨hp⟩
  have hbig : 2 < p := lt_of_le_of_ne hp.two_le hp2.symm
  have hunit : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hbig)
  have form (i : ℕ) : (t i : ZMod p) + c = 2 ^ i * c := by
    induction i with
    | zero => simp [hstart]
    | succ i ih => rw [hstep, pow_succ]; linear_combination 2 * ih
  have he := form (p - 1)
  rw [ZMod.pow_card_sub_one_eq_one hunit, one_mul] at he
  have hz : (t (p - 1) : ZMod p) = 0 := by linear_combination he
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hgt : p < t (p - 1) := calc
    p = t 0 := hstart.symm
    _ < t (p - 1) := hg (by omega)
  intro ht
  exact hgt.ne ((Nat.prime_dvd_prime_iff_eq hp ht).mp hdiv)

private theorem first_grows (p : ℕ) : StrictMono (firstKindTerm p) :=
  strictMono_nat_of_lt_succ fun i => by simp only [firstKindTerm]; omega

private theorem second_ge_two {p : ℕ} (hp : 2 ≤ p) (i : ℕ) : 2 ≤ secondKindTerm p i := by
  induction i with
  | zero => exact hp
  | succ i ih => simp only [secondKindTerm]; omega

private theorem second_grows {p : ℕ} (hp : 2 ≤ p) : StrictMono (secondKindTerm p) :=
  strictMono_nat_of_lt_succ fun i => by
    have := second_ge_two hp i
    simp only [secondKindTerm]
    omega

/-- Each odd prime seed has a nonprime term at index p − 1 in both chains. -/
theorem both_nonprime_at_pred_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬(firstKindTerm p (p - 1)).Prime ∧ ¬(secondKindTerm p (p - 1)).Prime := by
  constructor
  · apply composite_at_pred hp hp2 _ rfl (first_grows p) 1
    intro i
    simp [firstKindTerm]
  · apply composite_at_pred hp hp2 _ rfl (second_grows hp.two_le) (-1)
    intro i
    have hb := second_ge_two hp.two_le i
    rw [secondKindTerm, Nat.cast_sub (by omega : 1 ≤ 2 * secondKindTerm p i)]
    push_cast
    ring

/-- A long prime prefix can be followed to its first nonprime. Reading the last
k primes then gives an exact-length seed arbitrarily far up the increasing orbit. -/
private theorem infinitude_iff_prefixes (t : ℕ → ℕ → ℕ) (start : ∀ p, t p 0 = p)
    (shift : ∀ p j i, t (t p j) i = t p (j + i))
    (grows : ∀ p, p.Prime → StrictMono (t p))
    (stops : ∀ p, p.Prime → ∃ i, ¬(t p i).Prime) :
    (∀ k : ℕ, 0 < k → {p : ℕ | 0 < k ∧ (∀ i < k, (t p i).Prime) ∧ ¬(t p k).Prime}.Infinite) ↔
      ∀ L : ℕ, ∃ p : ℕ, ∀ i < L, (t p i).Prime := by
  constructor
  · intro h L
    obtain ⟨p, _, hp, _⟩ := (h (L + 1) (by omega)).nonempty
    exact ⟨p, fun i hi => hp i (by omega)⟩
  · intro h k hk
    apply Set.infinite_of_forall_exists_gt
    intro B
    obtain ⟨p, hprefix⟩ := h (B + k + 1)
    have hp : p.Prime := start p ▸ hprefix 0 (by omega)
    let term := stops p hp
    let last := Nat.find term
    have hlast : ¬(t p last).Prime := Nat.find_spec term
    have hlong : B + k < last := by
      by_contra! he
      exact hlast (hprefix last (by omega))
    let j := last - k
    have hj : j + k = last := Nat.sub_add_cancel (by omega)
    refine ⟨t p j, ⟨hk, ?_, ?_⟩, ?_⟩
    · intro i hi
      rw [shift]
      exact not_not.mp (Nat.find_min term (show j + i < last by omega))
    · simpa only [shift, hj] using hlast
    · have hle : j ≤ t p j := (grows p hp).id_le j
      omega

/-- For the first kind, Jones's full conjecture is equivalent to the existence
of one prime prefix of each length. -/
theorem firstKind_infinitude_iff_unbounded_prefixes :
    (type_of% @infinitely_many_firstKind_chains) ↔
      ∀ L : ℕ, ∃ p : ℕ, ∀ i < L, (firstKindTerm p i).Prime := by
  refine infinitude_iff_prefixes firstKindTerm (fun _ => rfl) ?_ (fun p _ => first_grows p) ?_
  · intro p j i
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun x : ℕ => 2 * x + 1) ih
  · intro p hp
    by_cases h : p = 2
    · subst p
      exact ⟨5, two_starts_firstKind_length_five.2.2⟩
    · exact ⟨p - 1, (both_nonprime_at_pred_of_odd_prime hp h).1⟩

/-- For the second kind, Jones's full conjecture is equivalent to the existence
of one prime prefix of each length. -/
theorem secondKind_infinitude_iff_unbounded_prefixes :
    (type_of% @infinitely_many_secondKind_chains) ↔
      ∀ L : ℕ, ∃ p : ℕ, ∀ i < L, (secondKindTerm p i).Prime := by
  refine infinitude_iff_prefixes secondKindTerm (fun _ => rfl) ?_ (fun _ hp => second_grows hp.two_le) ?_
  · intro p j i
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun x : ℕ => 2 * x - 1) ih
  · intro p hp
    by_cases h : p = 2
    · subst p
      exact ⟨3, by decide⟩
    · exact ⟨p - 1, (both_nonprime_at_pred_of_odd_prime hp h).2⟩

#print axioms both_nonprime_at_pred_of_odd_prime
#print axioms firstKind_infinitude_iff_unbounded_prefixes
#print axioms secondKind_infinitude_iff_unbounded_prefixes

end CunninghamChain
