import Erdos722QuadSwitchDoubling

/-!
# Distances between independently switched doublings

A change on one base block replaces all eight of its transversal blocks.
The one-sided block difference therefore recovers the Hamming distance exactly.
-/

namespace Erdos722.QuadSwitch
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V] {H : Finset (Finset V)}
variable (hH : H.IsBlockDesign 3 4)

omit [DecidableEq V] [Fintype V] in
private theorem distinct_parities (i : H) {b c : Bool} (h : b ≠ c) :
    Disjoint (component hH i b) (component hH i c) := by
  cases b <;> cases c
  · contradiction
  · exact tile_disjoint _
  · exact (tile_disjoint _).symm
  · contradiction

theorem component_mem_iff (bits : H → Bool) (i : H) {b : Bool} {D : Finset (V × Bool)}
    (h : D ∈ component hH i b) : D ∈ doubling hH bits ↔ b = bits i := by
  constructor
  · intro hd
    rcases (mem_doubling hH bits D).mp hd with ⟨P,hp,rfl⟩ | ⟨j,hj⟩
    · have eq := (footprint_twins P).symm.trans (component_shape hH i h).2
      have hc := hH.1 i.val i.property
      rw [← eq] at hc
      omega
    · have eq : j = i := Subtype.ext ((component_shape hH j hj).2.symm.trans (component_shape hH i h).2)
      subst j
      by_contra ne
      exact disjoint_left.mp (distinct_parities hH i ne) h hj
  · rintro rfl
    exact (mem_doubling hH bits _).mpr (.inr ⟨i,h⟩)

theorem difference (f g : H → Bool) :
    doubling hH f \ doubling hH g =
      (univ.filter fun i => f i ≠ g i).biUnion (fun i => component hH i (f i)) := by
  ext D
  constructor
  · intro hd
    obtain ⟨hf,hg⟩ := mem_sdiff.mp hd
    rcases (mem_doubling hH f D).mp hf with hp | ⟨i,hi⟩
    · exact (hg ((mem_doubling hH g D).mpr (.inl hp))).elim
    · exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,fun eq => hg ((component_mem_iff hH g i hi).mpr eq)⟩,hi⟩
  · intro hd
    obtain ⟨i,hi,hm⟩ := mem_biUnion.mp hd
    exact mem_sdiff.mpr ⟨(component_mem_iff hH f i hm).mpr rfl,
      fun hg => (mem_filter.mp hi).2 ((component_mem_iff hH g i hm).mp hg)⟩

/-- One-sided block distance is eight times the number of changed base bits. -/
theorem distance (f g : H → Bool) :
    (doubling hH f \ doubling hH g).card = 8 * (univ.filter fun i => f i ≠ g i).card := by
  rw [difference,card_biUnion]
  · simp [component,tile_card,Nat.mul_comm]
  · intro i _ j _ hij
    apply disjoint_left.mpr
    intro D hi hj
    exact hij (Subtype.ext ((component_shape hH i hi).2.symm.trans (component_shape hH j hj).2))

theorem doubling_injective : Function.Injective (doubling hH) := by
  intro f g e
  funext i
  have hc : (component hH i (f i)).card = 8 := tile_card _ _
  obtain ⟨D,hd⟩ := card_pos.mp (show 0 < (component hH i (f i)).card by omega)
  exact (component_mem_iff hH g i hd).mp (e ▸ (component_mem_iff hH f i hd).mpr rfl)

/-- The entire labelled cube on the doubled ground set. -/
theorem labelled_cube (hH : H.IsBlockDesign 3 4) : ∃ family : Finset (Finset (Finset (V × Bool))),
    family.card = 2^H.card ∧ ∀ D ∈ family, D.IsBlockDesign 3 4 := by
  classical
  refine ⟨univ.image (doubling hH),?_,?_⟩
  · rw [card_image_of_injective _ (doubling_injective hH)]
    simp
  · intro D hd
    obtain ⟨f,_,rfl⟩ := mem_image.mp hd
    exact doubling_design hH f

#print axioms difference
#print axioms distance
#print axioms doubling_injective
#print axioms labelled_cube
end Erdos722.QuadSwitch
