import Mathlib.Tactic

/-!
# The sign supports of a finite trade

If the signed weights through every set of at most r points sum to zero,
every nonzero weighting has at least 2^r distinct blocks of each sign.
Splitting at one point yields two nonzero trades of one smaller strength.
This form of the minimum trade bound permits a nonuniform block family.
-/

namespace Erdos722.Trade
open Finset
variable {V : Type*} [DecidableEq V]

def row (F : Finset (Finset V)) (w : Finset V → ℤ) (I : Finset V) : ℤ :=
  ∑ B ∈ F, if I ⊆ B then w B else 0

private theorem both_signs {F : Finset (Finset V)} {w : Finset V → ℤ}
    (hz : row F w ∅ = 0) (hn : ∃ B ∈ F, w B ≠ 0) :
    (∃ B ∈ F, 0 < w B) ∧ ∃ B ∈ F, w B < 0 := by
  have zero : ∑ B ∈ F, w B = 0 := by simpa [row] using hz
  obtain ⟨B,hB,ne⟩ := hn
  constructor
  · by_contra! h
    have less := sum_neg' h ⟨B,hB,lt_of_le_of_ne (h B hB) ne⟩
    omega
  · by_contra! h
    have more := sum_pos' h ⟨B,hB,lt_of_le_of_ne (h B hB) ne.symm⟩
    omega

private theorem row_through (F : Finset (Finset V)) (w : Finset V → ℤ) (x : V) (I : Finset V) :
    row (F.filter (x ∈ ·)) w I = row F w (insert x I) := by
  unfold row
  rw [sum_filter]
  apply sum_congr rfl
  intro B _
  by_cases h : x ∈ B <;> simp [h,insert_subset_iff]

private theorem row_split (F : Finset (Finset V)) (w : Finset V → ℤ) (x : V) (I : Finset V) :
    row (F.filter (x ∈ ·)) w I + row (F.filter (x ∉ ·)) w I = row F w I := by
  unfold row
  rw [← sum_union (disjoint_filter_filter_not ..),filter_union_filter_not_eq]

private theorem count_split (F : Finset (Finset V)) (P : Finset V → Prop) [DecidablePred P] (x : V) :
    ((F.filter (x ∈ ·)).filter P).card + ((F.filter (x ∉ ·)).filter P).card = (F.filter P).card := by
  simpa only [filter_filter, and_comm] using
    (card_filter_add_card_filter_not (s:=F.filter P) (fun B => x ∈ B))

/-- Distinct blocks of each sign, irrespective of the magnitudes of the nonzero weights. -/
theorem minimum_support (r : ℕ) (F : Finset (Finset V)) (w : Finset V → ℤ)
    (hz : ∀ I : Finset V, I.card ≤ r → row F w I = 0) (hn : ∃ B ∈ F, w B ≠ 0) :
    2^r ≤ (F.filter (fun B => 0 < w B)).card ∧ 2^r ≤ (F.filter (fun B => w B < 0)).card := by
  induction r generalizing F with
  | zero =>
    obtain ⟨⟨B,hB,hpos⟩,⟨C,hC,hneg⟩⟩ := both_signs (hz ∅ (by simp)) hn
    exact ⟨card_pos.mpr ⟨B,mem_filter.mpr ⟨hB,hpos⟩⟩,card_pos.mpr ⟨C,mem_filter.mpr ⟨hC,hneg⟩⟩⟩
  | succ r ih =>
    obtain ⟨⟨B,hB,hpos⟩,⟨C,hC,hneg⟩⟩ := both_signs (hz ∅ (by simp)) hn
    have ne : B ≠ C := fun e => (e ▸ hpos).not_gt hneg
    obtain ⟨x,hx⟩ : ∃ x, ¬(x ∈ B ↔ x ∈ C) := by
      by_contra! h
      exact ne (Finset.ext h)
    let F₁ := F.filter (x ∈ ·)
    let F₀ := F.filter (x ∉ ·)
    have witnesses : (∃ D ∈ F₁, w D ≠ 0) ∧ ∃ D ∈ F₀, w D ≠ 0 := by
      by_cases hb : x ∈ B
      · have hc : x ∉ C := fun hc => hx ⟨fun _ => hc, fun _ => hb⟩
        exact ⟨⟨B,mem_filter.mpr ⟨hB,hb⟩,hpos.ne'⟩,⟨C,mem_filter.mpr ⟨hC,hc⟩,hneg.ne⟩⟩
      · have hc : x ∈ C := by by_contra h; exact hx (iff_of_false hb h)
        exact ⟨⟨C,mem_filter.mpr ⟨hC,hc⟩,hneg.ne⟩,⟨B,mem_filter.mpr ⟨hB,hb⟩,hpos.ne'⟩⟩
    have z₁ (I : Finset V) (hI : I.card ≤ r) : row F₁ w I = 0 :=
      (row_through F w x I).trans (hz _ ((card_insert_le ..).trans (by omega)))
    have z₀ (I : Finset V) (hI : I.card ≤ r) : row F₀ w I = 0 := by
      have h := row_split F w x I
      change row F₁ w I + row F₀ w I = row F w I at h
      simpa only [z₁ I hI,zero_add,hz I (by omega)] using h
    obtain ⟨p₁,n₁⟩ := ih F₁ z₁ witnesses.1
    obtain ⟨p₀,n₀⟩ := ih F₀ z₀ witnesses.2
    rw [pow_succ]
    constructor
    · exact (by simpa only [Nat.mul_two] using add_le_add p₁ p₀ : 2^r * 2 ≤ _).trans_eq
        (count_split F (fun D => 0 < w D) x)
    · exact (by simpa only [Nat.mul_two] using add_le_add n₁ n₀ : 2^r * 2 ≤ _).trans_eq
        (count_split F (fun D => w D < 0) x)

#print axioms minimum_support
end Erdos722.Trade
