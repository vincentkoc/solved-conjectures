import CunninghamSeedAffineMask
import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

/-! Affine forms for both pinned recurrences at the selected translated seeds. -/

namespace CunninghamChain.SeedClusters

def seedTerm (first : Bool) := if first then firstKindTerm else secondKindTerm

private lemma term_pos (first : Bool) {u : ℕ} (hu : 0<u) (j : ℕ) : 0<seedTerm first u j := by
  cases first <;> induction j with
  | zero => simpa [seedTerm,firstKindTerm,secondKindTerm]
  | succ j ih => simp only [seedTerm,Bool.false_eq_true,if_false,if_true,firstKindTerm,secondKindTerm] at *;omega

lemma term_translate (first : Bool) {u : ℕ} (hu : 0<u) (x j : ℕ) :
    seedTerm first (x+u) j = 2^j*x + seedTerm first u j := by
  induction j with
  | zero => cases first <;> simp [seedTerm,firstKindTerm,secondKindTerm]
  | succ j ih =>
    have hp := term_pos first hu j
    cases first <;> simp only [seedTerm,Bool.false_eq_true,if_false,if_true,firstKindTerm,
      secondKindTerm,pow_succ',Nat.mul_assoc] at * <;> omega

lemma nonproportional_step (first : Bool) {u : ℕ} (hu : 0<u) (j h : ℕ) :
    2^(j+1)*h ≠ seedTerm first u (j+1) := by
  have hp := term_pos first hu j
  cases first <;> simp only [seedTerm,Bool.false_eq_true,if_false,if_true,firstKindTerm,
      secondKindTerm,pow_succ',Nat.mul_assoc] at * <;> omega

open Finset

private def forbiddenForms (A : Finset ℕ) (D H : ℕ) : Finset (ℕ × ℕ) :=
  ((range (D+1) \ A).image fun i => (1,i)) ∪
    A.biUnion (fun u => (range H).biUnion fun j =>
    {(2^(j+1),seedTerm true u (j+1)), (2^(j+1),seedTerm false u (j+1))})

private theorem coefficients (A : Finset ℕ) {D H : ℕ} (apos : ∀ u∈A, 0<u)
    {f : ℕ × ℕ} (hf : f∈forbiddenForms A D H) :
    0<f.1 ∧ ∀ v∈A, f.1*v ≠ f.2 := by
  rcases mem_union.mp hf with inactive | active
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp inactive
    refine ⟨by simp,?_⟩
    intro v hv e
    have eq : v=i := by simpa using e
    exact (mem_sdiff.mp hi).2 (eq ▸ hv)
  · obtain ⟨u,hu,hu'⟩ := mem_biUnion.mp active
    obtain ⟨j,_,pair⟩ := mem_biUnion.mp hu'
    simp only [mem_insert,mem_singleton] at pair
    rcases pair with rfl|rfl
    · exact ⟨by dsimp;positivity,fun v _ => nonproportional_step true (apos u hu) j v⟩
    · exact ⟨by dsimp;positivity,fun v _ => nonproportional_step false (apos u hu) j v⟩

/-- The unselected seed sites and H steps on both orbits from every selected seed
are composite on one progression; the selected translates remain admissible. -/
theorem orbit_mask (A : Finset ℕ) (D H : ℕ) (apos : ∀ u∈A, 0<u)
    (adm : ∀ p : ℕ, p.Prime → ∃ x, ∀ u∈A, ¬p ∣ x+u) :
    ∃ W B : ℕ, 0<W ∧ 2≤B ∧
      (∀ n i, i≤D → i∉A → ¬(W*n+B+i).Prime) ∧
      (∀ n u, u∈A → ∀ b : Bool, ∀ j<H, ¬(seedTerm b (W*n+B+u) (j+1)).Prime) ∧
      ∀ p : ℕ, p.Prime → ∃ n, ∀ u∈A, ¬p ∣ W*n+B+u := by
  let F := forbiddenForms A D H
  obtain ⟨W,B,wp,bp,forced,allowed⟩ := affine_mask A F Prod.fst Prod.snd adm
    (fun _ hf => (coefficients A apos hf).1) (fun _ hf => (coefficients A apos hf).2)
  refine ⟨W,B,wp,bp,?_,?_,allowed⟩
  · intro n i hi out
    have h : (1,i)∈F := mem_union_left _ (mem_image.mpr
      ⟨i,mem_sdiff.mpr ⟨mem_range.mpr (by omega),out⟩,rfl⟩)
    simpa using forced n _ h
  · intro n u hu b j hj
    have h : (2^(j+1),seedTerm b u (j+1))∈F := by
      apply mem_union_right
      refine mem_biUnion.mpr ⟨u,hu,mem_biUnion.mpr ⟨j,mem_range.mpr hj,?_⟩⟩
      cases b <;> simp
    rw [term_translate b (apos u hu)]
    exact forced n _ h

#print axioms orbit_mask

#print axioms term_translate
#print axioms nonproportional_step

end CunninghamChain.SeedClusters
