import FormalConjectures.Arxiv.«1104.1579».CunninghamChain
import FormalConjectures.Paper.PrimeTuples

/-! Local obstructions to first-kind Cunningham chains of exact length in a residue class. -/

namespace CunninghamChain

private theorem terms_modEq {d s r : ℕ} (h : s ≡ r [MOD d]) (i : ℕ) :
    firstKindTerm s i ≡ firstKindTerm r i [MOD d] := by
  induction i with
  | zero => exact h
  | succ i ih => exact (ih.mul_left 2).add_right 1

private theorem terms_increase (s : ℕ) : StrictMono (firstKindTerm s) :=
  strictMono_nat_of_lt_succ fun i => by simp only [firstKindTerm]; omega

private theorem coprime_at_large_seed {d r s i : ℕ} (hd : 0 < d) (hs : d < s)
    (hr : s ≡ r [MOD d]) (hp : (firstKindTerm s i).Prime) : (firstKindTerm r i).Coprime d := by
  rw [Nat.coprime_iff_gcd_eq_one, ← (terms_modEq hr i).gcd_eq]
  have hle : s ≤ firstKindTerm s i := (terms_increase s).monotone (Nat.zero_le i)
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hd (hs.trans_le hle))

/-- For primes outside the modulus, the fixed residue −1 avoids every prefix term. -/
private theorem prime_prefixes_in_class
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) {d r k : ℕ}
    (hd : 0 < d) (hk : 0 < k) (hcop : ∀ i < k, (firstKindTerm r i).Coprime d) :
    {s : ℕ | s ≡ r [MOD d] ∧ ∀ i < k, (firstKindTerm s i).Prime}.Infinite := by
  let idx (j : Fin (k + 1)) := j.val % k
  let a (j : Fin (k + 1)) : ℕ+ := ⟨2 ^ idx j * d, Nat.mul_pos (by positivity) hd⟩
  let c (j : Fin (k + 1)) := firstKindTerm r (idx j)
  have affine (i n : ℕ) :
      firstKindTerm (d * n + r) i = 2 ^ i * d * n + firstKindTerm r i := by
    induction i with
    | zero => simp [firstKindTerm]
    | succ i ih => rw [firstKindTerm, ih, firstKindTerm, pow_succ]; ring
  have form (j : Fin (k + 1)) (n : ℕ) : a j * n + c j = firstKindTerm (d * n + r) (idx j) :=
    (affine _ _).symm
  have adm (p : ℕ) (hp : p.Prime) : ∃ n, ¬p ∣ ∏ j, (a j * n + c j) := by
    by_cases hpd : p ∣ d
    · refine ⟨0, hp.prime.not_dvd_finsetProd fun j _ h => ?_⟩
      simp only [mul_zero, zero_add] at h
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt h hpd (hcop _ (Nat.mod_lt _ hk))
    · let : Fact p.Prime := ⟨hp⟩
      have hu : (d : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (-((r : ZMod p) + 1) / (d : ZMod p))
      have fixed (i : ℕ) : (firstKindTerm (d * n + r) i : ZMod p) = -1 := by
        induction i with
        | zero => simp only [firstKindTerm, Nat.cast_add, Nat.cast_mul, hn]; field_simp; ring
        | succ i ih => simp only [firstKindTerm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_one, ih]; ring
      refine ⟨n, hp.prime.not_dvd_finsetProd fun j _ => ?_⟩
      rw [form, ← ZMod.natCast_eq_zero_iff, fixed]
      simp
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n, hn, hnB⟩ := Set.infinite_iff_exists_gt.mp (hD (by omega : 2 ≤ k + 1) a c adm) B
  refine ⟨d * n + r, ⟨by simp [Nat.ModEq, Nat.add_mod], ?_⟩, ?_⟩
  · intro i hi
    let j : Fin (k + 1) := ⟨i, by omega⟩
    simpa [form, idx, j, Nat.mod_eq_of_lt hi] using hn j
  · have := Nat.le_mul_of_pos_left n hd
    omega

/-- If the stopping term has a fixed divisor in the class, every sufficiently large
prime prefix in that class already has exact length. -/
private theorem exact_of_obstruction
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) {d r k : ℕ}
    (hd : 0 < d) (hk : 0 < k) (hcop : ∀ i < k, (firstKindTerm r i).Coprime d)
    (hstop : ¬(firstKindTerm r k).Coprime d) :
    {s : ℕ | s ≡ r [MOD d] ∧ IsFirstKindChainOfLength s k}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨s, ⟨hr, hp⟩, hs⟩ := Set.infinite_iff_exists_gt.mp
    (prime_prefixes_in_class hD hd hk hcop) (max B d)
  refine ⟨s, ⟨hr, hk, hp, fun h => hstop (coprime_at_large_seed hd ?_ hr h)⟩, ?_⟩ <;> omega

/-- A failed prefix coprimality test leaves at most one seed, unconditionally.
At the obstructed index, a prime term must equal the fixed gcd with the modulus. -/
theorem subsingleton_firstKind_chains_in_class_of_not_coprime {d r k i : ℕ}
    (hi : i < k) (hbad : ¬(firstKindTerm r i).Coprime d) :
    {s : ℕ | s ≡ r [MOD d] ∧ IsFirstKindChainOfLength s k}.Subsingleton := by
  have forced {s : ℕ} (hr : s ≡ r [MOD d]) (hc : IsFirstKindChainOfLength s k) :
      firstKindTerm s i = (firstKindTerm r i).gcd d := by
    have hp := hc.2.1 i hi
    rw [← (terms_modEq hr i).gcd_eq]
    apply (Nat.gcd_eq_left ?_).symm
    by_contra h
    apply hbad
    rw [Nat.coprime_iff_gcd_eq_one, ← (terms_modEq hr i).gcd_eq]
    exact hp.coprime_iff_not_dvd.mpr h
  have inj (j : ℕ) : Function.Injective (fun s => firstKindTerm s j) := by
    induction j with
    | zero => exact fun _ _ h => h
    | succ j ih =>
      intro a b h
      exact ih (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (Nat.add_right_cancel h))
  rintro s ⟨hs, hsc⟩ t ⟨ht, htc⟩
  exact inj i ((forced hs hsc).trans (forced ht htc).symm)

/-- Under Dickson, exact length k occurs infinitely often in a residue class precisely
when all k prefix terms at its representative are coprime to the modulus. -/
theorem infinite_firstKind_chains_in_class_iff
    (hD : type_of% @PrimeTuplesConjecture.prime_tuples_conjecture) (d r k : ℕ)
    (hd : 0 < d) (hk : 0 < k) :
    {s : ℕ | s ≡ r [MOD d] ∧ IsFirstKindChainOfLength s k}.Infinite ↔
      ∀ i < k, (firstKindTerm r i).Coprime d := by
  constructor
  · intro hinf i hi
    by_contra h
    exact hinf (subsingleton_firstKind_chains_in_class_of_not_coprime hi h).finite
  · intro hcop
    by_cases hlast : (firstKindTerm r k).Coprime d
    · have hall : ∀ i < k + 1, (firstKindTerm r i).Coprime d := by
        intro i hi
        rcases Nat.lt_or_eq_of_le (by omega : i ≤ k) with h | rfl
        · exact hcop i h
        · exact hlast
      obtain ⟨b, hb, _⟩ := Set.infinite_iff_exists_gt.mp
        (prime_prefixes_in_class hD hd (by omega) hall) d
      obtain ⟨hbr, hb⟩ := hb
      let q := firstKindTerm b k
      have hq : q.Prime := hb k (by omega)
      have hpre (i : ℕ) (hi : i < k) : (firstKindTerm b i).Coprime (d * q) := by
        apply Nat.coprime_mul_iff_right.mpr
        refine ⟨?_, (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
          (hb i (by omega)).pos (terms_increase b hi))).symm⟩
        rw [Nat.coprime_iff_gcd_eq_one, (terms_modEq hbr i).gcd_eq]
        exact hcop i hi
      have bad : ¬q.Coprime (d * q) :=
        fun h => (hq.coprime_iff_not_dvd.mp h) (dvd_mul_left _ _)
      apply (exact_of_obstruction hD (Nat.mul_pos hd hq.pos) hk hpre bad).mono
      rintro s ⟨hs, hc⟩
      exact ⟨(hs.of_dvd (dvd_mul_right d q)).trans hbr, hc⟩
    · exact exact_of_obstruction hD hd hk hcop hlast

#print axioms subsingleton_firstKind_chains_in_class_of_not_coprime
#print axioms infinite_firstKind_chains_in_class_iff

end CunninghamChain
