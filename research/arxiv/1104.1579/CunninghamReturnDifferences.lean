import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! A set meeting the positive differences of every sufficiently large finite
set has finitely many translates covering a tail of the natural numbers. -/

namespace CunninghamChain.PrimeReturns
open Finset

/-- At least one positive difference from every set of K positions lies in G. -/
def MeetsDifferences (G : Set ℕ) (K : ℕ) : Prop :=
  ∀ A : Finset ℕ, K ≤ A.card → ∃ i ∈ A, ∃ j ∈ A, i < j ∧ j-i ∈ G

/-- The translates are indexed by a maximal set whose positive differences
avoid G. Fewer than K translates suffice, regardless of their diameter. -/
theorem finite_translates_cover (G : Set ℕ) (K : ℕ) (h : MeetsDifferences G K) :
    ∃ A : Finset ℕ, A.card < K ∧ ∀ n > A.sup id, ∃ i ∈ A, n-i ∈ G := by
  classical
  let Avoid (A : Finset ℕ) := ∀ i ∈ A, ∀ j ∈ A, i < j → j-i ∉ G
  have hsmall {A : Finset ℕ} (ha : Avoid A) : A.card < K := by
    by_contra! hh
    obtain ⟨i,hi,j,hj,hij,hd⟩ := h A hh
    exact ha i hi j hj hij hd
  let P (c : ℕ) := ∃ A : Finset ℕ, Avoid A ∧ A.card=c
  have hz : P 0 := ⟨∅, by simp [Avoid], by simp⟩
  obtain ⟨A,hA,hmax⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le K) hz
  refine ⟨A,hsmall hA,?_⟩
  intro n hn
  have hlt {i : ℕ} (hi : i ∈ A) : i<n := (le_sup (f := id) hi).trans_lt hn
  by_contra! hno
  have hnext : Avoid (insert n A) := by
    intro i hi j hj hij
    rcases mem_insert.mp hi with hin | hiA
    · rcases mem_insert.mp hj with hjn | hjA
      · omega
      · have := hlt hjA; omega
    · rcases mem_insert.mp hj with hjn | hjA
      · rw [hjn]; exact hno i hiA
      · exact hA i hiA j hjA hij
  have hnmem : n ∉ A := fun hh => (hlt hh).false
  have hcard := card_insert_of_notMem hnmem
  have hl := Nat.le_findGreatest (P := P) (hsmall hnext).le ⟨_,hnext,rfl⟩
  omega

theorem bounded_gaps_of_meetsDifferences {G : Set ℕ} {K : ℕ} (h : MeetsDifferences G K) :
    ∃ D : ℕ, ∀ n, ∃ d ∈ G, n ≤ d ∧ d ≤ n+D := by
  obtain ⟨A,_,hcover⟩ := finite_translates_cover G K h
  refine ⟨A.sup id+1, ?_⟩
  intro n
  obtain ⟨i,hi,hd⟩ := hcover (n+A.sup id+1) (by omega)
  have hle : i ≤ A.sup id := le_sup (f := id) hi
  exact ⟨_,hd,by omega,by omega⟩

#print axioms finite_translates_cover
#print axioms bounded_gaps_of_meetsDifferences

private def AllDifferences (G : Set ℕ) (B : Finset ℕ) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, i < j → j-i ∈ G

private theorem extend_differences {G : Set ℕ} {B : Finset ℕ} {a : ℕ}
    (h : AllDifferences G B) (ha : ∀ i ∈ B, a < i ∧ i-a ∈ G) : AllDifferences G (insert a B) := by
  intro i hi j hj hij
  rcases mem_insert.mp hi with hia | hiB
  · rcases mem_insert.mp hj with hja | hjB
    · omega
    · simpa [hia] using (ha j hjB).2
  · rcases mem_insert.mp hj with hja | hjB
    · have := (ha i hiB).1; omega
    · exact h i hiB j hjB hij

/-- The finite two-color Ramsey argument with pairs colored by their positive difference. -/
private theorem difference_ramsey (G : Set ℕ) (k l : ℕ) :
    ∃ M : ℕ, ∀ A : Finset ℕ, M ≤ A.card →
      (∃ U ⊆ A, k ≤ U.card ∧ AllDifferences G U) ∨
      (∃ V ⊆ A, l ≤ V.card ∧ AllDifferences Gᶜ V) := by
  classical
  induction k generalizing l with
  | zero => exact ⟨0,fun A _ => Or.inl ⟨∅,empty_subset _,by simp,by simp [AllDifferences]⟩⟩
  | succ k ih =>
    induction l with
    | zero => exact ⟨0,fun A _ => Or.inr ⟨∅,empty_subset _,by simp,by simp [AllDifferences]⟩⟩
    | succ l jh =>
      obtain ⟨m,hm⟩ := ih (l+1)
      obtain ⟨n,hn⟩ := jh
      refine ⟨m+n+1, ?_⟩
      intro A hcard
      have ha : A.Nonempty := card_pos.mp (by omega)
      let a := A.min' ha
      have haA : a ∈ A := min'_mem _ _
      let E := A.erase a
      let F := E.filter (fun j => j-a ∈ G)
      have hFA : F ⊆ A := (filter_subset ..).trans (erase_subset ..)
      have hEA : E ⊆ A := erase_subset ..
      have hlt {i} (hi : i ∈ E) : a < i :=
        lt_of_le_of_ne (min'_le _ _ (hEA hi)) (mem_erase.mp hi).1.symm
      by_cases hsize : m ≤ F.card
      · rcases hm F hsize with ⟨U,hU,hu,hg⟩ | ⟨V,hV,hv,hg⟩
        · have hed (i) (hi : i ∈ U) := mem_filter.mp (hU hi)
          have hnot : a ∉ U := fun hh => (hlt (hed a hh).1).false
          exact Or.inl ⟨insert a U, insert_subset haA (hU.trans hFA),
            by rw [card_insert_of_notMem hnot]; omega,
            extend_differences hg (fun i hi => ⟨hlt (hed i hi).1,(hed i hi).2⟩)⟩
        · exact Or.inr ⟨V,hV.trans hFA,hv,hg⟩
      · let J := E \ F
        have hdiff : J.card = E.card-F.card := card_sdiff_of_subset (filter_subset ..)
        have hE : E.card = A.card-1 := card_erase_of_mem haA
        rcases hn J (by omega) with ⟨U,hU,hu,hg⟩ | ⟨V,hV,hv,hg⟩
        · exact Or.inl ⟨U,hU.trans (sdiff_subset.trans hEA),hu,hg⟩
        · have hed (i) (hi : i ∈ V) := mem_sdiff.mp (hV hi)
          have hnot : a ∉ V := fun hh => (hlt (hed a hh).1).false
          refine Or.inr ⟨insert a V,insert_subset haA (hV.trans (sdiff_subset.trans hEA)),
            by rw [card_insert_of_notMem hnot]; omega, extend_differences hg ?_⟩
          intro i hi
          exact ⟨hlt (hed i hi).1, fun hg' => (hed i hi).2 (mem_filter.mpr ⟨(hed i hi).1,hg'⟩)⟩

/-- The finite difference-set property survives intersections, unlike bounded
gaps alone. This permits a common set of spacings for several recurrence conditions. -/
theorem meetsDifferences_inter {G H : Set ℕ} {k l : ℕ} (hg : MeetsDifferences G k)
    (hh : MeetsDifferences H l) : ∃ M, MeetsDifferences (G ∩ H) M := by
  obtain ⟨M,hm⟩ := difference_ramsey G l k
  refine ⟨M,?_⟩
  intro A hA
  rcases hm A hA with ⟨U,hu,hct,hpos⟩ | ⟨V,hv,hct,hneg⟩
  · obtain ⟨i,hi,j,hj,hij,hd⟩ := hh U hct
    exact ⟨i,hu hi,j,hu hj,hij,hpos i hi j hj hij,hd⟩
  · obtain ⟨i,hi,j,hj,hij,hd⟩ := hg V hct
    exact False.elim ((hneg i hi j hj hij) hd)

#print axioms meetsDifferences_inter

/-- Scaling the positions preserves the difference property for the pullback
set of spacings, for every positive integer scaling factor. -/
theorem meetsDifferences_dilate {G : Set ℕ} {K s : ℕ} (hg : MeetsDifferences G K)
    (hs : 0 < s) : MeetsDifferences {d | s*d ∈ G} K := by
  classical
  intro A hA
  let B := A.image (s*·)
  have hc : B.card = A.card := card_image_of_injective _ (mul_right_injective₀ hs.ne')
  obtain ⟨x,hx,y,hy,hlt,hd⟩ := hg B (hc ▸ hA)
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
  refine ⟨i,hi,j,hj,lt_of_mul_lt_mul_left' hlt, ?_⟩
  change s*(j-i)∈G
  rwa [Nat.mul_sub]

#print axioms meetsDifferences_dilate

end CunninghamChain.PrimeReturns
