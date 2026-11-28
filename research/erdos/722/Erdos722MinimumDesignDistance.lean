import Erdos722MinimumTradeSupport
import Erdos722SubsetIncidence
import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite

/-!
# Minimum difference of packings with the same incidence counts

The lower incidence rows of a constant-size family follow by double counting.
Thus two different k-uniform families with identical r-subset counts must
lose at least 2^r blocks in each direction. This includes ordinary designs.
-/

namespace Erdos722.Trade
open Finset IntegralDesign
variable {V : Type*} [DecidableEq V]

/-- A nonzero signed trade on the k-layer, given just its top incidence equations. -/
theorem layer_minimum (U : Finset V) {r k : ℕ} (hrk : r ≤ k) (w : Finset V → ℤ)
    (hz : ∀ I ∈ U.powersetCard r, incidence U k w I = 0)
    (hn : ∃ B ∈ U.powersetCard k, w B ≠ 0) :
    2^r ≤ ((U.powersetCard k).filter (fun B => 0 < w B)).card ∧
    2^r ≤ ((U.powersetCard k).filter (fun B => w B < 0)).card := by
  apply minimum_support r _ w _ hn
  intro I hI
  have zero : incidence U r (incidence U k w) I = 0 :=
    sum_eq_zero fun A hA => hz A (mem_filter.mp hA).1
  rw [incidence_incidence U I hI w] at zero
  have nz : (((k-I.card).choose (r-I.card) : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hrk I.card)).ne'
  have h := (mul_eq_zero.mp zero).resolve_left nz
  simpa [row,incidence,sum_filter] using h

def countThrough (F : Finset (Finset V)) (I : Finset V) := (F.filter (I ⊆ ·)).card

variable [Fintype V]

private theorem count_row (F : Finset (Finset V)) {k : ℕ} (hk : ∀ B ∈ F, B.card = k) (I : Finset V) :
    incidence univ k (fun B => if B ∈ F then (1 : ℤ) else 0) I = countThrough F I := by
  unfold incidence countThrough
  rw [← sum_filter]
  have eq : (((univ : Finset V).powersetCard k).filter (I ⊆ ·)).filter (· ∈ F) = F.filter (I ⊆ ·) := by
    ext B
    simp only [mem_filter,mem_powersetCard,subset_univ,true_and]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hk B h.1,h.2⟩,h.1⟩⟩
  simp [eq]

/-- Both one-sided distances for two distinct packings with equal top-row counts. -/
theorem packing_distance {F G : Finset (Finset V)} {r k : ℕ}
    (hrk : r ≤ k) (hf : ∀ B ∈ F, B.card = k) (hg : ∀ B ∈ G, B.card = k)
    (he : ∀ I : Finset V, I.card = r → countThrough F I = countThrough G I)
    (ne : F ≠ G) : 2^r ≤ (F \ G).card ∧ 2^r ≤ (G \ F).card := by
  let w := fun B : Finset V => (if B ∈ F then (1 : ℤ) else 0) - (if B ∈ G then 1 else 0)
  let U := (univ : Finset V).powersetCard k
  have zero (I : Finset V) (hI : I ∈ (univ : Finset V).powersetCard r) : incidence univ k w I = 0 := by
    change (∑ B ∈ _, ((if B ∈ F then (1 : ℤ) else 0) - (if B ∈ G then 1 else 0))) = 0
    rw [sum_sub_distrib]
    change incidence univ k _ I - incidence univ k _ I = 0
    rw [count_row F hf,count_row G hg,he I (mem_powersetCard.mp hI).2,sub_self]
  obtain ⟨B,hB⟩ : ∃ B, ¬(B ∈ F ↔ B ∈ G) := by
    by_contra! h
    exact ne (Finset.ext h)
  have nz : ∃ B ∈ U, w B ≠ 0 := by
    refine ⟨B,?_,?_⟩
    · apply mem_powersetCard.mpr
      refine ⟨subset_univ _,?_⟩
      by_cases h : B ∈ F
      · exact hf B h
      · exact hg B (by by_contra e; exact hB (iff_of_false h e))
    · by_cases h₁ : B ∈ F <;> by_cases h₂ : B ∈ G <;> simp_all [w]
  have pos : U.filter (fun B => 0 < w B) = F \ G := by
    ext B
    by_cases h₁ : B ∈ F <;> by_cases h₂ : B ∈ G <;> simp [U,w,h₁,h₂,hf,hg]
  have neg : U.filter (fun B => w B < 0) = G \ F := by
    ext B
    by_cases h₁ : B ∈ F <;> by_cases h₂ : B ∈ G <;> simp [U,w,h₁,h₂,hf,hg]
  exact pos ▸ neg ▸ layer_minimum univ hrk w zero nz

omit [Fintype V] in
private theorem design_count {F : Finset (Finset V)} {r k : ℕ} (h : F.IsBlockDesign r k)
    (I : Finset V) (hi : I.card = r) : countThrough F I = 1 := by
  apply card_eq_one_iff_existsUnique.mpr
  simpa only [mem_filter] using h.2 I hi

theorem design_distance {F G : Finset (Finset V)} {r k : ℕ} (hrk : r ≤ k)
    (hf : F.IsBlockDesign r k) (hg : G.IsBlockDesign r k) (ne : F ≠ G) :
    2^r ≤ (F \ G).card ∧ 2^r ≤ (G \ F).card :=
  packing_distance hrk hf.1 hg.1 (fun I hi => (design_count hf I hi).trans (design_count hg I hi).symm) ne

#print axioms layer_minimum
#print axioms packing_distance
#print axioms design_distance
end Erdos722.Trade
