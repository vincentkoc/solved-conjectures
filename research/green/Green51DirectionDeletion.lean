import Green51Hyperplane

/-! # Minimum deletions to remove one direction from a binary double -/

namespace Green51DeletionRadius
open Finset Green53ParityThreshold
open scoped Classical Pointwise

variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Inputs paired with another occupied input in direction `z`. -/
def mates (A : Finset G) (z : G) : Finset G := A.filter fun x => x + z ∈ A

omit [DecidableEq G] in
private theorem back (a z : G) : a + z + z = a := by rw [add_assoc, ZModModule.add_self, add_zero]

/-- Removing a direction requires a deletion at one endpoint of each disjoint pair. -/
theorem direction_cost {A B : Finset G} (z : G) (absent : z ∉ B + B) :
    (mates A z).card ≤ 2 * (A \ B).card := by
  let E := A \ B
  have both (x : G) (hx : x ∈ B) (hp : x + z ∈ B) : False := by
    apply absent
    exact mem_add.mpr ⟨x, hx, x + z, hp, by rw [←add_assoc, ZModModule.add_self, zero_add]⟩
  have sub : mates A z ⊆ E ∪ E.map (Equiv.addRight z).toEmbedding := by
    intro x h
    obtain ⟨ha, hmate⟩ := mem_filter.mp h
    by_cases hb : x ∈ B
    · exact mem_union_right _ (mem_map.mpr ⟨x + z, mem_sdiff.mpr ⟨hmate, both x hb⟩, back x z⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨ha, hb⟩)
  simpa [E, two_mul] using (card_le_card sub).trans (card_union_le E _)

/-- For a nonzero direction, selecting one endpoint per pair attains the bound exactly. -/
theorem attainable_cost [Fintype G] (A : Finset G) (z : G) (nz : z ≠ 0) :
    ∃ B ⊆ A, z ∉ B + B ∧ 2 * (A \ B).card = (mates A z).card := by
  let num := Fintype.equivFin G
  let R := mates A z
  let E := R.filter fun x => num x < num (x + z)
  have flip {x : G} (hx : x ∈ R) : x + z ∈ R := by
    obtain ⟨ha, hm⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hm, (back x z).symm ▸ ha⟩
  have ne (x : G) : num (x + z) ≠ num x := by
    intro h
    apply nz
    exact add_left_cancel (show x + z = x + 0 by simpa using num.injective h)
  have split : R = E ∪ E.map (Equiv.addRight z).toEmbedding := by
    ext x
    constructor
    · intro hx
      rcases lt_or_gt_of_ne (ne x) with lt | gt
      · exact mem_union_right _ (mem_map.mpr ⟨x + z, mem_filter.mpr ⟨flip hx, by simpa only [back] using lt⟩, back x z⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hx, gt⟩)
    · rintro hx
      rcases mem_union.mp hx with h | h
      · exact (mem_filter.mp h).1
      · obtain ⟨y, hy, rfl⟩ := mem_map.mp h
        exact flip (mem_filter.mp hy).1
  have dis : Disjoint E (E.map (Equiv.addRight z).toEmbedding) := by
    rw [Finset.disjoint_left]
    intro x hx him
    obtain ⟨y, hy, rfl⟩ := mem_map.mp him
    have f := (mem_filter.mp hy).2
    have g : num (y + z) < num ((y + z) + z) := (mem_filter.mp hx).2
    exact (not_lt_of_gt f) (by simpa only [back] using g)
  have eA : E ⊆ A := fun x hx => (mem_filter.mp (mem_filter.mp hx).1).1
  refine ⟨A \ E, sdiff_subset, ?_, ?_⟩
  · intro hz
    obtain ⟨a, ha, b, hb, eq⟩ := mem_add.mp hz
    have bval : b = a + z := by rw [←eq, ←add_assoc, ZModModule.add_self, zero_add]
    subst b
    have member : a ∈ R := mem_filter.mpr ⟨(mem_sdiff.mp ha).1, (mem_sdiff.mp hb).1⟩
    rw [split] at member
    rcases mem_union.mp member with deleted | shifted
    · exact (mem_sdiff.mp ha).2 deleted
    · obtain ⟨y, hy, hyval⟩ := mem_map.mp shifted
      have aplus : a + z = y := by change y + z = a at hyval; rw [←hyval, back]
      exact (mem_sdiff.mp hb).2 (aplus.symm ▸ hy)
  · have lost : A \ (A \ E) = E := by ext x; simp; tauto
    rw [lost]
    change 2 * E.card = R.card
    rw [split, card_union_of_disjoint dis, card_map, two_mul]

end Green51DeletionRadius
#print axioms Green51DeletionRadius.direction_cost
#print axioms Green51DeletionRadius.attainable_cost
