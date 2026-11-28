import Green51GeelenEquality

/-! # Circuit fibres of diameter two -/

namespace Green51SliceExtrema
open Finset
open scoped Classical symmDiff
variable {α : Type*} [DecidableEq α]
private theorem partner {P : Finset α} {x : α} (hp : P.card = 2) (hx : x ∈ P) :
    ∃ y, y ≠ x ∧ P = {x, y} := by
  obtain ⟨u, v, uv, rfl⟩ := card_eq_two.mp hp
  rcases mem_insert.mp hx with rfl | hv
  · exact ⟨v, uv.symm, rfl⟩
  · obtain rfl := mem_singleton.mp hv
    exact ⟨u, uv, pair_comm _ _⟩


/-- A family of at least five binary supports at pairwise distance zero or two lies in one radius-one sphere. -/
theorem rich_slice (C : Finset α) (J : Finset (Finset α))
    (inside : ∀ S ∈ J, S ⊆ C)
    (dist : ∀ S ∈ J, ∀ R ∈ J, (S ∆ R).card = 0 ∨ (S ∆ R).card = 2) (rich : 5 ≤ J.card) :
    ∃ T ⊆ C, J ⊆ C.image fun x => T ∆ {x} := by
  classical
  obtain ⟨R, hr⟩ := card_pos.mp (show 0 < J.card by omega)
  let transl (S : Finset α) := R ∆ S
  have inv (S : Finset α) : transl (transl S) = S := symmDiff_symmDiff_cancel_left _ _
  have inj := Function.LeftInverse.injective inv
  let W := J.image transl
  let E := W.erase ∅
  have empty : ∅ ∈ W := mem_image.mpr ⟨R, hr, by simp [transl]⟩
  have order : E.card + 1 = J.card := by
    have w : W.card = J.card := card_image_of_injective _ inj
    have erase := card_erase_of_mem empty
    have ne := card_pos.mpr (show W.Nonempty from ⟨∅, empty⟩)
    dsimp only [E]; omega
  have within (S) (hs : S ∈ W) : S ⊆ C := by
    obtain ⟨U, hu, rfl⟩ := mem_image.mp hs
    intro x hx
    rcases mem_symmDiff.mp hx with h | h
    · exact inside R hr h.1
    · exact inside U hu h.1
  have two (P) (hp : P ∈ E) : P.card = 2 := by
    obtain ⟨ne, hw⟩ := mem_erase.mp hp
    obtain ⟨U, hu, rfl⟩ := mem_image.mp hw
    rcases dist R hr U hu with zero | ok
    · exact (ne (card_eq_zero.mp zero)).elim
    · exact ok
  have meet (P) (hp : P ∈ E) (Q) (hq : Q ∈ E) : ∃ x, x ∈ P ∧ x ∈ Q := by
    by_contra! no
    have dis : Disjoint P Q := disjoint_left.mpr no
    have length : (P ∆ Q).card = 4 := by
      rw [Finset.symmDiff_def, sdiff_eq_self_of_disjoint dis, sdiff_eq_self_of_disjoint dis.symm,
        card_union_of_disjoint dis, two P hp, two Q hq]
    obtain ⟨U, hu, pu⟩ := mem_image.mp (mem_erase.mp hp).2
    obtain ⟨V, hv, qv⟩ := mem_image.mp (mem_erase.mp hq).2
    have eq : P ∆ Q = U ∆ V := by rw [←pu, ←qv]; simp [transl, symmDiff_symmDiff_symmDiff_comm]
    rw [eq] at length
    rcases dist U hu V hv with zero | tw; all_goals omega
  obtain ⟨u, hu⟩ := (star_or_triangle E two meet).resolve_right (by omega)
  obtain ⟨P, hp⟩ := card_pos.mp (show 0 < E.card by omega)
  have uc := within P (mem_erase.mp hp).2 (hu P hp)
  have substar : E ⊆ (C.erase u).image (fun v => ({u, v} : Finset α)) := by
    intro S hs
    obtain ⟨v, vu, rfl⟩ := partner (two S hs) (hu S hs)
    exact mem_image.mpr ⟨v, mem_erase.mpr ⟨vu, within _ (mem_erase.mp hs).2 (mem_insert_of_mem (mem_singleton_self _))⟩, rfl⟩
  refine ⟨R ∆ {u}, ?_, ?_⟩
  · intro x hx
    rcases mem_symmDiff.mp hx with h | h
    · exact inside R hr h.1
    · simpa [mem_singleton.mp h.1] using uc
  · intro S hs
    have sw : transl S ∈ W := mem_image.mpr ⟨S, hs, rfl⟩
    by_cases zero : transl S = ∅
    · refine mem_image.mpr ⟨u, uc, ?_⟩
      have h := inv S; rw [zero] at h
      have same : R = S := by simpa [transl, Finset.symmDiff_def] using h
      simpa [symmDiff_assoc] using same
    · have se : transl S ∈ E := mem_erase.mpr ⟨zero, sw⟩
      have edge := substar se
      obtain ⟨v, hv, eq⟩ := mem_image.mp edge
      refine mem_image.mpr ⟨v, (mem_erase.mp hv).2, ?_⟩
      have diff : ({u} : Finset α) ∆ {v} = {u, v} := by
        ext x; simp [mem_symmDiff]; grind [(mem_erase.mp hv).1]
      rw [symmDiff_assoc, diff, eq]
      exact inv S

end Green51SliceExtrema
#print axioms Green51SliceExtrema.rich_slice

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold Green51SliceExtrema
open scoped Classical Pointwise symmDiff

variable {G V : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
  [AddCommGroup V] [Module F V] [DecidableEq V]

/-- Describe the fibre over a quotient point using the circuit words of its representative. -/
theorem coded_fibre {D C : Finset G} (m : ShortestOddCircuit D C) (π : G →ₗ[F] V)
    (ker : π.ker = Submodule.span F (C : Set G)) (a : G) :
    D.filter (fun x => π x = π a) = (sliceWords D C {a}).image (sliceValue {a}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨xd, same⟩ := mem_filter.mp hx
    have v : x + a ∈ Submodule.span F (C : Set G) := by rw [←ker, LinearMap.mem_ker, map_add, same, ZModModule.add_self]
    obtain ⟨U, uc, rep⟩ := subset_sum C (x + a) v
    have chosen : ∃ T ⊆ C, Even T.card ∧ (∑ t ∈ T, t) = x + a := by
      by_cases par : Even U.card
      · exact ⟨U, uc, par, rep⟩
      · have n := card_sdiff_add_card_eq_card uc
        have o := m.2.1
        exact ⟨C \ U, sdiff_subset, by rw [Nat.even_iff] at par ⊢; rw [Nat.odd_iff] at o; omega,
          (circuit_complement_sum uc m.2.2.1).trans rep⟩
    obtain ⟨T, tc, even, val⟩ := chosen
    have eq : sliceValue {a} T = x := by rw [sliceValue, sum_singleton, val, add_assoc, ZModModule.add_self, add_zero]
    exact mem_image.mpr ⟨T, mem_filter.mpr ⟨mem_powerset.mpr tc, by rw [card_singleton, Nat.odd_iff]; rw [Nat.even_iff] at even; omega, eq.symm ▸ xd⟩, eq⟩
  · intro hx
    obtain ⟨S, hs, rfl⟩ := mem_image.mp hx
    obtain ⟨sc, _, xd⟩ := mem_filter.mp hs
    have z : (∑ s ∈ S, s) ∈ π.ker := by
      rw [ker]
      exact Submodule.sum_mem _ fun _ h => Submodule.subset_span (mem_powerset.mp sc h)
    exact mem_filter.mpr ⟨xd, by rw [sliceValue, sum_singleton, map_add, LinearMap.mem_ker.mp z, zero_add]⟩

/-- Represent a fibre of size at least five by distinct letters of one translated circuit. -/
theorem rich_fibre {D C : Finset G} (m : ShortestOddCircuit D C) (π : G →ₗ[F] V)
    (ker : π.ker = Submodule.span F (C : Set G)) (a : G)
    (rich : 5 ≤ (D.filter (fun x => π x = π a)).card) :
    ∃ t : G, π t = π a ∧ ∃ I ⊆ C, (D.filter (fun x => π x = π a)).card ≤ I.card ∧ ∀ i ∈ I, t + i ∈ D := by
  let J := sliceWords D C {a}
  have within (S : Finset G) (hs : S ∈ J) : S ⊆ C := mem_powerset.mp (mem_filter.mp hs).1
  have dist (S : Finset G) (hs : S ∈ J) (R : Finset G) (hr : R ∈ J) : (S ∆ R).card = 0 ∨ (S ∆ R).card = 2 := by
    obtain ⟨_, so, sx⟩ := mem_filter.mp hs
    obtain ⟨_, ro, rx⟩ := mem_filter.mp hr
    have bound := slice_dist m (within S hs) (within R hr) so ro sx rx rfl rfl
    obtain ⟨parts, par⟩ := card_symmDiff_parts S R
    rw [Nat.odd_iff] at so ro
    omega
  have coded := coded_fibre m π ker a
  rw [coded] at rich
  obtain ⟨T, tc, subset⟩ := rich_slice C J within dist (rich.trans card_image_le)
  let t := sliceValue {a} T
  let I := C.filter fun i => t + i ∈ D
  have inc : (D.filter (fun x => π x = π a)) ⊆ I.image (fun i => t + i) := by
    intro x hx
    obtain ⟨S, hs, eq⟩ := mem_image.mp (coded ▸ hx)
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (subset hs)
    have val : sliceValue {a} (T ∆ {i}) = t + i := by dsimp [t, sliceValue]; rw [sum_word, sum_singleton, add_right_comm]
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, (val.symm.trans eq).symm ▸ (mem_filter.mp hx).1⟩, val.symm.trans eq⟩
  have z : (∑ i ∈ T, i) ∈ π.ker := by rw [ker]; exact Submodule.sum_mem _ fun _ h => Submodule.subset_span (tc h)
  exact ⟨t, by rw [show t = (∑ i ∈ T, i) + a by simp [t, sliceValue], map_add, LinearMap.mem_ker.mp z, zero_add],
    I, filter_subset _ _, (card_le_card inc).trans card_image_le, fun _ hi => (mem_filter.mp hi).2⟩

end Green51GirthFrame
#print axioms Green51GirthFrame.coded_fibre
#print axioms Green51GirthFrame.rich_fibre
