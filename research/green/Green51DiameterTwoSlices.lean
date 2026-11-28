import Mathlib

/-! # Pairwise intersecting edges and the size of a same-parity diameter-two slice -/
open Finset
open scoped Classical symmDiff
namespace Green51SliceExtrema
variable {α : Type*} [DecidableEq α]

private theorem other_end {P : Finset α} {x : α} (hp : P.card = 2) (hx : x ∈ P) :
    ∃ y, y ≠ x ∧ P = {x, y} := by
  obtain ⟨u, v, uv, rfl⟩ := card_eq_two.mp hp
  rcases mem_insert.mp hx with rfl | hv
  · exact ⟨v, uv.symm, rfl⟩
  · obtain rfl := mem_singleton.mp hv
    exact ⟨u, uv, pair_comm _ _⟩

/-- Pairwise intersecting edges share a vertex or form a family of at most three. -/
theorem star_or_triangle (E : Finset (Finset α)) (pairs : ∀ P ∈ E, P.card = 2)
    (meet : ∀ P ∈ E, ∀ Q ∈ E, ∃ x, x ∈ P ∧ x ∈ Q) :
    (∃ x, ∀ P ∈ E, x ∈ P) ∨ E.card ≤ 3 := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | ⟨P, hp⟩
  · exact .inr (by simp)
  obtain ⟨u, v, uv, rfl⟩ := card_eq_two.mp (pairs P hp)
  by_cases au : ∀ Q ∈ E, u ∈ Q
  · exact .inl ⟨u, au⟩
  by_cases av : ∀ Q ∈ E, v ∈ Q
  · exact .inl ⟨v, av⟩
  push Not at au av
  obtain ⟨Q, hq, nqu⟩ := au
  obtain ⟨R, hr, nrv⟩ := av
  have vq : v ∈ Q := by
    obtain ⟨x, xp, xq⟩ := meet _ hp Q hq
    simp only [mem_insert, mem_singleton] at xp
    rcases xp with rfl | rfl
    · contradiction
    · exact xq
  have ur : u ∈ R := by
    obtain ⟨x, xp, xr⟩ := meet _ hp R hr
    simp only [mem_insert, mem_singleton] at xp
    rcases xp with rfl | rfl
    · exact xr
    · contradiction
  obtain ⟨w, wv, rfl⟩ := other_end (pairs Q hq) vq
  obtain ⟨y, yu, rfl⟩ := other_end (pairs R hr) ur
  have eq : w = y := by
    obtain ⟨x, xq, xr⟩ := meet _ hq _ hr
    simp only [mem_insert, mem_singleton] at xq xr nqu nrv
    grind
  subst y
  right
  have subset : E ⊆ ({{u, v}, {v, w}, {u, w}} : Finset (Finset α)) := by
    intro P hp'
    obtain ⟨a, b, ab, rfl⟩ := card_eq_two.mp (pairs P hp')
    obtain ⟨x, xp, xv⟩ := meet _ hp' _ hp
    obtain ⟨y, yp, yw⟩ := meet _ hp' _ hq
    obtain ⟨z, zp, zw⟩ := meet _ hp' _ hr
    simp only [mem_insert, mem_singleton] at xp xv yp yw zp zw nqu nrv ⊢
    grind [pair_comm]
  exact (card_le_card subset).trans ((card_insert_le _ _).trans (by
    have := card_insert_le ({v, w} : Finset α) ({{u, w}} : Finset (Finset α))
    simp only [card_singleton] at this
    omega))

/-- A largest intersecting edge family on at least five vertices is a full star. -/
theorem edge_bound (C : Finset α) (hc : 5 ≤ C.card) (E : Finset (Finset α))
    (inside : ∀ S ∈ E, S ⊆ C) (pairs : ∀ P ∈ E, P.card = 2)
    (meet : ∀ P ∈ E, ∀ Q ∈ E, ∃ x, x ∈ P ∧ x ∈ Q) :
    E.card + 1 ≤ C.card ∧ (E.card + 1 = C.card → ∃ u ∈ C, E = (C.erase u).image fun v => {u, v}) := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | ⟨P, hp⟩
  · simp only [card_empty, zero_add]
    exact ⟨by omega, by omega⟩
  rcases star_or_triangle E pairs meet with ⟨u, star⟩ | little
  · have uc := inside P hp (star P hp)
    let whole := (C.erase u).image fun v => ({u, v} : Finset α)
    have sub : E ⊆ whole := by
      intro S hs
      obtain ⟨v, vu, rfl⟩ := other_end (pairs S hs) (star S hs)
      exact mem_image.mpr ⟨v, mem_erase.mpr ⟨vu, inside _ hs (mem_insert_of_mem (mem_singleton_self _))⟩, rfl⟩
    have cap : whole.card ≤ C.card - 1 := card_image_le.trans_eq (card_erase_of_mem uc)
    have order := card_le_card sub
    exact ⟨by omega, fun equality => ⟨u, uc, eq_of_subset_of_card_le sub (show whole.card ≤ E.card by omega)⟩⟩
  · exact ⟨by omega, by omega⟩

/-- A diameter-two family in one parity class has at most one word per coordinate.
Equality characterizes the translates of the singleton words. -/
theorem slice_bound (C : Finset α) (hc : 5 ≤ C.card) (J : Finset (Finset α))
    (inside : ∀ S ∈ J, S ⊆ C)
    (dist : ∀ S ∈ J, ∀ R ∈ J, (S ∆ R).card = 0 ∨ (S ∆ R).card = 2) :
    J.card ≤ C.card ∧ (J.card = C.card →
      ∃ T ⊆ C, J = C.image fun x => T ∆ {x}) := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | ⟨R, hr⟩
  · simp only [card_empty, zero_le, true_and]
    omega
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
  obtain ⟨bound, rigid⟩ := edge_bound C hc E (fun P hp => within P (mem_erase.mp hp).2) two meet
  refine ⟨by omega, ?_⟩
  intro saturates
  obtain ⟨u, uc, full⟩ := rigid (by omega)
  refine ⟨R ∆ {u}, ?_, ?_⟩
  · intro x hx
    rcases mem_symmDiff.mp hx with h | h
    · exact inside R hr h.1
    · simpa [mem_singleton.mp h.1] using uc
  ext S
  constructor
  · intro hs
    have sw : transl S ∈ W := mem_image.mpr ⟨S, hs, rfl⟩
    by_cases zero : transl S = ∅
    · refine mem_image.mpr ⟨u, uc, ?_⟩
      have h := inv S; rw [zero] at h
      have same : R = S := by simpa [transl, Finset.symmDiff_def] using h
      simpa [symmDiff_assoc] using same
    · have se : transl S ∈ E := mem_erase.mpr ⟨zero, sw⟩
      rw [full] at se
      obtain ⟨v, hv, eq⟩ := mem_image.mp se
      refine mem_image.mpr ⟨v, (mem_erase.mp hv).2, ?_⟩
      have diff : ({u} : Finset α) ∆ {v} = {u, v} := by
        ext x; simp [mem_symmDiff]; grind [(mem_erase.mp hv).1]
      rw [symmDiff_assoc, diff, eq]
      exact inv S
  · rintro hs
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hs
    by_cases vu : v = u
    · simpa [vu, symmDiff_assoc] using hr
    · have diff : ({u} : Finset α) ∆ {v} = {u, v} := by
        ext x; simp [mem_symmDiff]; grind
      have se : {u, v} ∈ E := by rw [full]; exact mem_image.mpr ⟨v, mem_erase.mpr ⟨vu, hv⟩, rfl⟩
      obtain ⟨U, hu, eq⟩ := mem_image.mp (mem_erase.mp se).2
      rw [symmDiff_assoc, diff, ←eq]
      change transl (transl U) ∈ J
      rwa [inv]
end Green51SliceExtrema
#print axioms Green51SliceExtrema.star_or_triangle
#print axioms Green51SliceExtrema.edge_bound
#print axioms Green51SliceExtrema.slice_bound
