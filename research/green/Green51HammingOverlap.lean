import Green51ThresholdExample
import Green51DirectionDeletion

/-! # Minimum overlap of a Hamming cylinder with a translate in its double -/

namespace Green51DeletionRadius
open Finset
open scoped Classical symmDiff
variable {ι : Type*} [DecidableEq ι]

/-- Subsets of a coordinate face of weight at most `s`. -/
def lowerHalf (U : Finset ι) (s : ℕ) := U.powerset.filter fun S => S.card ≤ s

/-- Counting the lower half includes the central layer. -/
theorem lowerHalf_card (s : ℕ) (U : Finset ι) (dim : U.card = 2 * s) :
    2 * (lowerHalf U s).card = 2 ^ (2 * s) + (2 * s).choose s := by
  let L := U.powerset.filter fun S => S.card < s
  let H := U.powerset.filter fun S => s < S.card
  let M := U.powersetCard s
  have count : L.card = H.card := by
    apply card_bij (fun S _ => U \ S)
    · intro S hs
      obtain ⟨inc, sl⟩ := mem_filter.mp hs
      have sub := mem_powerset.mp inc
      exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, by rw [card_sdiff_of_subset sub, dim]; omega⟩
    · intro S hs T ht eq
      have ss := mem_powerset.mp (mem_filter.mp hs).1
      have st := mem_powerset.mp (mem_filter.mp ht).1
      ext i
      have hh := Finset.ext_iff.mp eq i
      simp only [mem_sdiff] at hh
      exact ⟨fun h => by by_contra hn; exact (hh.mpr ⟨ss h, hn⟩).2 h,
        fun h => by by_contra hn; exact (hh.mp ⟨st h, hn⟩).2 h⟩
    · intro T ht
      obtain ⟨inc, sl⟩ := mem_filter.mp ht
      have sub := mem_powerset.mp inc
      have bound := card_le_card sub
      rw [dim] at bound
      refine ⟨U \ T, mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, ?_⟩, ?_⟩
      · rw [card_sdiff_of_subset sub, dim]; omega
      · ext i
        simp only [mem_sdiff]
        exact ⟨fun h => by by_contra hh; exact h.2 ⟨h.1, hh⟩,
          fun h => ⟨sub h, fun pre => pre.2 h⟩⟩
  have eq : lowerHalf U s = L ∪ M := by
    ext S
    simp only [lowerHalf, L, M, mem_filter, mem_powerset, mem_union, mem_powersetCard]
    by_cases h : S ⊆ U <;> simp [h]; omega
  have dis : Disjoint L M := by
    rw [disjoint_left]
    intro S hl hm
    exact (mem_filter.mp hl).2.ne (mem_powersetCard.mp hm).2
  have partition : lowerHalf U s ∪ H = U.powerset := by
    ext S
    by_cases h : S ⊆ U <;> simp [lowerHalf, H, h, le_or_gt]
  have apart : Disjoint (lowerHalf U s) H := by
    rw [disjoint_left]
    exact fun S hl hh => (not_lt_of_ge (mem_filter.mp hl).2) (mem_filter.mp hh).2
  have total := congrArg Finset.card partition
  rw [card_union_of_disjoint apart, card_powerset, dim] at total
  have lower := congrArg Finset.card eq
  rw [card_union_of_disjoint dis, show M.card = (2 * s).choose s by simp [M, dim]] at lower
  omega

/-- Every direction in a face on `2 * s` coordinates retains a central layer of pairs. -/
theorem subcube_overlap (s : ℕ) (U T : Finset ι) (dim : U.card = 2 * s) (sub : T ⊆ U) :
    (2 * s).choose s ≤ ((lowerHalf U s).filter fun S => (S ∆ T).card ≤ s).card := by
  let L := lowerHalf U s
  let I := L.image fun S => S ∆ T
  have im {S : Finset ι} : S ∈ I ↔ S ∆ T ∈ L := by
    constructor
    · intro h
      obtain ⟨B, hb, rfl⟩ := mem_image.mp h
      simpa only [symmDiff_symmDiff_cancel_right] using hb
    · intro h
      exact mem_image.mpr ⟨S ∆ T, h, symmDiff_symmDiff_cancel_right _ _⟩
  have qs : L ∪ I ⊆ U.powerset := by
    intro S hs
    rcases mem_union.mp hs with hl | hi
    · exact (mem_filter.mp hl).1
    · obtain ⟨B, hb, rfl⟩ := mem_image.mp hi
      exact mem_powerset.mpr (symmDiff_subset_union.trans (union_subset (mem_powerset.mp (mem_filter.mp hb).1) sub))
  have li : L ∩ I = L.filter fun S => (S ∆ T).card ≤ s := by
    ext S
    simp only [mem_inter, mem_filter, im, L, lowerHalf, mem_powerset]
    constructor
    · tauto
    · rintro ⟨⟨ss, small⟩, dist⟩
      exact ⟨⟨ss, small⟩, symmDiff_subset_union.trans (union_subset ss sub), dist⟩
  have orig := lowerHalf_card s U dim
  have total := card_union_add_card_inter L I
  have hi : I.card = L.card := card_image_of_injective _ (symmDiff_left_injective _)
  have le := card_le_card qs
  rw [hi, li] at total
  rw [card_powerset, dim] at le
  change 2 * L.card = _ at orig
  change (2 * s).choose s ≤ (L.filter fun S => (S ∆ T).card ≤ s).card
  omega

open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical Pointwise symmDiff

/-- Every direction of the double has at least this many ordered representations. -/
theorem cylinder_overlap {s r : ℕ} (z : Fin (2 * (s + 1) + r) → F)
    (member : z ∈ ball (s + 1) r + ball (s + 1) r) :
    2 ^ r * (2 * s).choose s ≤ (mates (ball (s + 1) r) z).card := by
  let d := 2 * (s + 1)
  let T := (splitSupport d r z).1
  have weight : T.card + 2 ≤ d := (ball_sum_iff z).mp member
  obtain ⟨U, tu, _, us⟩ := exists_subsuperset_card_eq (subset_univ T) (show T.card ≤ 2 * s by dsimp [d] at weight; omega)
    (show 2 * s ≤ (univ : Finset (Fin d)).card by simp [d])
  let L := (lowerHalf U s).filter fun S => (S ∆ T).card ≤ s
  let V := (L ×ˢ (univ : Finset (Fin r → F))).map (splitSupport d r).symm.toEmbedding
  have inclusion : V ⊆ mates (ball (s + 1) r) z := by
    intro a ha
    obtain ⟨⟨S, y⟩, hin, rfl⟩ := mem_map.mp ha
    have hS := (mem_product.mp hin).1
    have sz := (mem_filter.mp (mem_filter.mp hS).1).2
    have dist := (mem_filter.mp hS).2
    change S.card ≤ s at sz
    change (S ∆ T).card ≤ s at dist
    refine mem_filter.mpr ⟨ball_mem.mpr ?_, ball_mem.mpr ?_⟩
    · simpa [d] using Nat.lt_succ_of_le sz
    · rw [support_add]
      simpa [T, d] using Nat.lt_succ_of_le dist
  have ct : V.card = 2 ^ r * L.card := by simp [V, F, mul_comm]
  have bound := card_le_card inclusion
  rw [ct] at bound
  exact (Nat.mul_le_mul_left _ (subcube_overlap s U T us tu)).trans bound

private theorem outer_intersection {ι : Type*} [DecidableEq ι] (s : ℕ) (T S : Finset ι)
    (st : T.card = 2 * s) :
    S.card ≤ s ∧ (S ∆ T).card ≤ s ↔ S ⊆ T ∧ S.card = s := by
  constructor
  · rintro ⟨sz, sd⟩
    have sub : T ⊆ S ∪ (S ∆ T) := by
      intro x hx; by_cases h : x ∈ S
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_symmDiff.mpr (Or.inr ⟨hx, h⟩))
    have cap := card_union_le S (S ∆ T)
    have lo := card_le_card sub
    have eq := eq_of_subset_of_card_le sub (show (S ∪ (S ∆ T)).card ≤ T.card by omega)
    exact ⟨eq.symm ▸ subset_union_left, by omega⟩
  · rintro ⟨sub, eq⟩
    have same : S ∆ T = T \ S := by ext i; simp [mem_symmDiff]; tauto
    rw [same, card_sdiff_of_subset sub, st, eq]
    omega

/-- A direction with `2 * s` active ones attains the lower bound exactly. -/
theorem outer_overlap {s r : ℕ} (z : Fin (2 * (s + 1) + r) → F)
    (wt : (splitSupport (2 * (s + 1)) r z).1.card = 2 * s) :
    (mates (ball (s + 1) r) z).card = 2 ^ r * (2 * s).choose s := by
  let d := 2 * (s + 1)
  let T := (splitSupport d r z).1
  have shape : mates (ball (s + 1) r) z =
      ((T.powersetCard s) ×ˢ (univ : Finset (Fin r → F))).map (splitSupport d r).symm.toEmbedding := by
    ext a
    simp only [mates, mem_filter, ball_mem, support_add, mem_map_equiv, Equiv.symm_symm,
      mem_product, mem_powersetCard, mem_univ, and_true, Nat.lt_succ_iff]
    exact outer_intersection s T _ wt
  rw [shape, card_map, card_product, card_powersetCard]
  simp [T, d, wt, F, mul_comm]

end Green51DeletionRadius
#print axioms Green51DeletionRadius.lowerHalf_card
#print axioms Green51DeletionRadius.subcube_overlap
#print axioms Green51DeletionRadius.cylinder_overlap
#print axioms Green51DeletionRadius.outer_overlap
