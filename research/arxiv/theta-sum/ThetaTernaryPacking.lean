import ThetaTernaryDeletion

/-! Extract disjoint representations at a fixed target after prescribed deletions. -/
namespace Arxiv.«2501.03234».ThetaTernaryPacking
open Finset ThetaTernaryDeletion

def vertices (t : ℕ × ℕ × ℕ) : Finset ℕ := {t.1,t.2.1,t.2.2}

private theorem few (t : ℕ × ℕ × ℕ) : (vertices t).card≤3 := by
  unfold vertices
  have h := card_insert_le t.1 ({t.2.1,t.2.2} : Finset ℕ)
  have hh := card_insert_le t.2.1 ({t.2.2} : Finset ℕ)
  simp only [card_singleton] at hh
  omega

private theorem support {A : Finset ℕ} {n : ℕ} {t : ℕ × ℕ × ℕ}
    (ht : t∈distinctTriples A n) : vertices t ⊆ A := by
  obtain ⟨ha,hb,hc,_⟩ := mem.mp (mem_filter.mp ht).1
  intro x hx;simp only [vertices,mem_insert,mem_singleton] at hx
  rcases hx with rfl|rfl|rfl;exact ha;exact hb;exact hc

private theorem enlarge {A B : Finset ℕ} (h : A ⊆ B) (n : ℕ) :
    distinctTriples A n ⊆ distinctTriples B n := by
  intro t ht
  obtain ⟨hh,hd⟩ := mem_filter.mp ht
  obtain ⟨ha,hb,hc,hn⟩ := mem.mp hh
  exact mem_filter.mpr ⟨mem.mpr ⟨h ha,h hb,h hc,hn⟩,hd⟩

/-- All three entries in each representation are different. Distinct
representations in the selected family also have disjoint vertex sets. -/
theorem pack (A : Finset ℕ) (n m : ℕ) (E : Finset ℕ)
    (hm : 3*(E.card+3*m+1)*A.card < (triples A A A n).card) :
    ∃ D ⊆ distinctTriples (A \ E) n,D.card=m ∧
      ∀ t∈D,∀ u∈D,t≠u → Disjoint (vertices t) (vertices u) := by
  classical
  induction m generalizing E with
  | zero => exact ⟨∅,empty_subset _,card_empty,by simp⟩
  | succ m ih =>
    have hd := distinct_deletion A E n
    have hl : 3*(E.card+1)*A.card ≤ 3*(E.card+3*(m+1)+1)*A.card := by gcongr;omega
    obtain ⟨t,ht⟩ := card_pos.mp (show 0<(distinctTriples (A \ E) n).card by omega)
    let B := E∪vertices t
    have hB : B.card≤E.card+3 := (card_union_le _ _).trans (Nat.add_le_add_left (few t) _)
    have hm' : 3*(B.card+3*m+1)*A.card < (triples A A A n).card := by
      apply lt_of_le_of_lt _ hm
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 (by omega))
    obtain ⟨D,hD,hcard,hpair⟩ := ih B hm'
    have hass {u : ℕ × ℕ × ℕ} (hu : u∈D) : Disjoint (vertices t) (vertices u) := by
      apply disjoint_left.mpr;intro v hv hw
      exact (mem_sdiff.mp (support (hD hu) hw)).2 (mem_union_right E hv)
    have hnot : t∉D := by
      intro hh
      have hv : t.1∈vertices t := by simp [vertices]
      exact disjoint_left.mp (hass hh) hv hv
    have hs : A \ B ⊆ A \ E := by
      intro v hv
      obtain ⟨ha,hn⟩ := mem_sdiff.mp hv
      exact mem_sdiff.mpr ⟨ha,fun he => hn (mem_union_left _ he)⟩
    refine ⟨insert t D,insert_subset ht (hD.trans (enlarge hs n)),by simp [hnot,hcard],?_⟩
    intro x hx y hy hne
    rcases mem_insert.mp hx with hxt|hxd
    · rcases mem_insert.mp hy with hyt|hyd
      · exact False.elim (hne (hxt.trans hyt.symm))
      · rw [hxt];exact hass hyd
    · rcases mem_insert.mp hy with hyt|hyd
      · rw [hyt];exact (hass hxd).symm
      · exact hpair x hxd y hyd hne

#print axioms pack
end Arxiv.«2501.03234».ThetaTernaryPacking
