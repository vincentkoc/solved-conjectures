import Green51FrameSections

/-! # Overlap of an odd binary circuit with a translate -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem even_zero_empty {C D E : Finset G} (m : ShortestOddCircuit D C)
    (sub : E ⊆ C) (par : Even E.card) (zero : (∑ x ∈ E, x) = 0) : E = ∅ := by
  have parts := card_sdiff_add_card_eq_card sub
  have odd := m.2.1
  have small := m.2.2.2 (C \ E) (sdiff_subset.trans m.1) (by
    rw [Nat.odd_iff] at odd ⊢
    rw [Nat.even_iff] at par
    omega) ((circuit_complement_sum sub m.2.2.1).trans zero)
  exact card_eq_zero.mp (by omega)

private theorem even_word_injective {C D A B : Finset G} (m : ShortestOddCircuit D C)
    (a : A ⊆ C) (b : B ⊆ C) (ha : Even A.card) (hb : Even B.card)
    (same : (∑ x ∈ A, x) = ∑ x ∈ B, x) : A = B := by
  have sub : A ∆ B ⊆ C := by
    intro x hx
    rcases mem_symmDiff.mp hx with h | h
    · exact a h.1
    · exact b h.1
  have ct := (card_symmDiff_parts A B).2
  have par : Even (A ∆ B).card := by
    rw [Nat.even_iff] at ha hb ⊢
    omega
  have eq := even_zero_empty m sub par (by rw [sum_word,same,ZModModule.add_self])
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hn
    have h : x ∈ A ∆ B := mem_symmDiff.mpr (Or.inl ⟨hx,hn⟩)
    rw [eq] at h
    exact Finset.notMem_empty x h
  · intro x hx
    by_contra hn
    have h : x ∈ A ∆ B := mem_symmDiff.mpr (Or.inr ⟨hx,hn⟩)
    rw [eq] at h
    exact Finset.notMem_empty x h

/-- A nonzero translate of an odd binary circuit meets it in at most two points. -/
theorem circuit_shift_overlap {C D : Finset G} (m : ShortestOddCircuit D C)
    (v : G) (nv : v ≠ 0) : (C.filter (fun x => x+v ∈ C)).card ≤ 2 := by
  classical
  let H := C.filter (fun x => x+v ∈ C)
  by_cases empty : H = ∅
  · change H.card ≤ 2
    simp [empty]
  obtain ⟨c,hc⟩ := nonempty_iff_ne_empty.mpr empty
  have pair (x : G) (hx : x ∈ H) :
      ({x,x+v} : Finset G) ⊆ C ∧ ({x,x+v} : Finset G).card=2 ∧
        (∑ z ∈ ({x,x+v} : Finset G), z) = v := by
    obtain ⟨a,b⟩ := mem_filter.mp hx
    have ne : x ≠ x+v := by
      intro e
      exact nv (add_left_cancel (show x+v=x+0 by simpa using e.symm))
    refine ⟨insert_subset a (singleton_subset_iff.mpr b),by simp [ne],?_⟩
    simp [ne,←add_assoc,ZModModule.add_self]
  have bound : H ⊆ {c,c+v} := by
    intro x hx
    obtain ⟨ax,sz,sx⟩ := pair x hx
    obtain ⟨ac,sc,eq⟩ := pair c hc
    have same := even_word_injective m ax ac (by rw [sz]; decide) (by rw [sc]; decide)
      (sx.trans eq.symm)
    rw [←same]
    exact mem_insert_self _ _
  exact (card_le_card bound).trans (pair c hc).2.1.le

end Green51OriginRecovery

#print axioms Green51OriginRecovery.circuit_shift_overlap
