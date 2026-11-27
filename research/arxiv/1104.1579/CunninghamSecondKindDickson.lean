import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import FormalConjectures.Paper.PrimeTuples
import Mathlib.NumberTheory.PrimesCongruentOne

/-! Exact termination for second-kind Cunningham chains under Dickson's conjecture.
Jones, *Polynomial Cunningham Chains*, §1 (arXiv:1104.1579). -/

namespace CunninghamChain

private theorem secondKindTerm_add_one (x i : ℕ) :
    secondKindTerm (x + 1) i = 2 ^ i * x + 1 := by
  induction i with
  | zero => simp [secondKindTerm]
  | succ i ih =>
    rw [secondKindTerm, ih, pow_succ, mul_right_comm (2 ^ i) 2 x]
    omega

/-- The fixed seed used in the local admissibility argument has no prime prefix. -/
theorem secondKindTerm_one (i : ℕ) : secondKindTerm 1 i = 1 := by
  simpa using secondKindTerm_add_one 0 i

/-- Dickson's prime-tuples conjecture implies Jones's exact-length statement of the second kind. -/
theorem infinitely_many_secondKind_chains_of_primeTuples
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) :
    type_of% @infinitely_many_secondKind_chains := by
  intro k hk
  -- Start with a prime q = 2^k * b + 1. Its earlier terms are positive and smaller than q.
  obtain ⟨q, hq, _, hcong⟩ := Nat.exists_prime_gt_modEq_one 1 (pow_ne_zero k (by decide : 2 ≠ 0))
  obtain ⟨b, hb⟩ := (Nat.modEq_iff_exists_eq_add hq.one_le).mp hcong.symm
  have hqb : q = 2 ^ k * b + 1 := by omega
  have hbpos : 0 < b := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hqb
    exact hq.ne_one hqb
  -- Duplicate the first form when k = 1, respecting Dickson's arity restriction.
  let idx (i : Fin (k + 1)) := i.val % k
  let a (i : Fin (k + 1)) : ℕ+ := ⟨2 ^ idx i * q, Nat.mul_pos (by positivity) hq.pos⟩
  let c (i : Fin (k + 1)) := 2 ^ idx i * b + 1
  have form (i : Fin (k + 1)) (n : ℕ) :
      a i * n + c i = 2 ^ idx i * (q * n + b) + 1 := by
    change 2 ^ idx i * q * n + (2 ^ idx i * b + 1) = _
    ring
  have admissible (p : ℕ) (hp : p.Prime) : ∃ n, ¬p ∣ ∏ i, (a i * n + c i) := by
    by_cases heq : p = q
    · subst p
      refine ⟨0, hq.prime.not_dvd_finsetProd fun i _ => ?_⟩
      rw [form]
      simp only [mul_zero, zero_add]
      apply Nat.not_dvd_of_pos_of_lt (by positivity)
      rw [hqb]
      exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right
        (Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ hk)) hbpos) _
    · let : Fact p.Prime := ⟨hp⟩
      have hunit : (q : ZMod p) ≠ 0 := by
        rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq hp hq]
      obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (-(b : ZMod p) / (q : ZMod p))
      have hz : (q : ZMod p) * n + b = 0 := by rw [hn]; field_simp; ring
      refine ⟨n, hp.prime.not_dvd_finsetProd fun i _ => ?_⟩
      rw [form, ← ZMod.natCast_eq_zero_iff]
      push_cast
      simp [hz]
  have hprime := hD (by omega : 2 ≤ k + 1) a c admissible
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n, hn, hnB⟩ := Set.infinite_iff_exists_gt.mp hprime B
  refine ⟨q * n + b + 1, ⟨hk, ?_, ?_⟩, ?_⟩
  · intro i hi
    let j : Fin (k + 1) := ⟨i, by omega⟩
    simpa [form, secondKindTerm_add_one, idx, j, Nat.mod_eq_of_lt hi] using hn j
  · rw [secondKindTerm_add_one, show 2 ^ k * (q * n + b) + 1 = q * (2 ^ k * n + 1) by
      calc
        _ = 2 ^ k * b + 1 + q * (2 ^ k * n) := by ring
        _ = _ := by rw [← hqb]; ring]
    have hpos : 0 < 2 ^ k * n := Nat.mul_pos (by positivity) (by omega)
    exact Nat.not_prime_mul hq.ne_one (by omega)
  · have := Nat.le_mul_of_pos_left n hq.pos
    omega

end CunninghamChain

#print axioms CunninghamChain.secondKindTerm_one
#print axioms CunninghamChain.infinitely_many_secondKind_chains_of_primeTuples
