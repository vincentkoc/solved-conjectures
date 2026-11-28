import Erdos722PointedFaces

/-!
# Transporting partial triple designs between pointed rectangles

The finite projections of a triple record all coordinates except the
distinguished point. Embedding the two sides preserves their cardinalities.
-/

namespace Erdos722.PointedProduct
open Finset Function

abbrev Grid (U V : Type*) := Option (U × V)

def leftTrace {U V : Type*} [DecidableEq U] (T : Finset (Grid U V)) : Finset U :=
  T.eraseNone.image Prod.fst

def rightTrace {U V : Type*} [DecidableEq V] (T : Finset (Grid U V)) : Finset V :=
  T.eraseNone.image Prod.snd

def gridMap {A B U V : Type*} (e : A ↪ U) (f : B ↪ V) : Grid A B ↪ Grid U V :=
  (e.prodMap f).optionMap

private theorem erase_map {A B : Type*} (e : A ↪ B) (T : Finset (Option A)) :
    (T.map e.optionMap).eraseNone=T.eraseNone.map e := by
  ext x
  simp only [mem_eraseNone,mem_map]
  constructor
  · rintro ⟨(_ | a),h,he⟩
    · cases he
    · exact ⟨a,h,Option.some.inj he⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨some a,ha,rfl⟩

theorem traces_map {A B U V : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq U] [DecidableEq V]
    (e : A ↪ U) (f : B ↪ V) (T : Finset (Grid A B)) :
    leftTrace (T.map (gridMap e f))=(leftTrace T).map e ∧
    rightTrace (T.map (gridMap e f))=(rightTrace T).map f := by
  simp only [leftTrace,rightTrace,gridMap,erase_map]
  simp only [map_eq_image,image_image]
  exact ⟨rfl,rfl⟩

/-- A point at infinity can occur at most once in a triple. -/
theorem traces_size {U V : Type*} [DecidableEq U] [DecidableEq V] {T : Finset (Grid U V)}
    (hT : T.card=3) : (0<(leftTrace T).card ∧ (leftTrace T).card≤3) ∧
      (0<(rightTrace T).card ∧ (rightTrace T).card≤3) := by
  classical
  have two : 0<T.eraseNone.card := by
    by_cases hn : none∈T
    · rw [card_eraseNone_of_mem hn,hT]; decide
    · rw [card_eraseNone_of_not_mem hn,hT]; decide
  have big := (card_eraseNone_le T).trans hT.le
  exact ⟨⟨card_pos.mpr ((card_pos.mp two).image _),card_image_le.trans big⟩,
    ⟨card_pos.mpr ((card_pos.mp two).image _),card_image_le.trans big⟩⟩

def localEvent {U V : Type*} [DecidableEq U] [DecidableEq V] (s t : Shape)
    (T : Finset (Grid U V)) : Prop :=
  s.accepts (leftTrace T).card ∧ t.accepts (rightTrace T).card

structure Tile (q : ℕ) (s t : Shape) where
  blocks : Finset (Finset (Grid (Fin (s.width q)) (Fin (t.width q))))
  size : ∀ B∈blocks, B.card=q+1
  inside : ∀ B∈blocks, ∀ T⊆B, T.card=3 → localEvent s t T
  cover : ∀ T, T.card=3 → localEvent s t T → ∃! B, B∈blocks ∧ T⊆B

variable {U V : Type*} [DecidableEq U] [DecidableEq V] {q : ℕ}
variable {H : Finset (Finset (Option U))} {J : Finset (Finset (Option V))}

def belongs (a : Face H) (b : Face J) (T : Finset (Grid U V)) : Prop :=
  fits a (leftTrace T) ∧ fits b (rightTrace T)

/-- Three points lie in exactly one pair of pointed faces. -/
theorem unique_pair (hH : H.IsBlockDesign 3 (q+1)) (hJ : J.IsBlockDesign 3 (q+1))
    {T : Finset (Grid U V)} (hT : T.card=3) :
    ∃! ab : Face H × Face J, belongs ab.1 ab.2 T := by
  obtain ⟨⟨hl,hl'⟩,hr,hr'⟩ := traces_size hT
  obtain ⟨a,ha,ua⟩ := unique_face hH hl hl'
  obtain ⟨b,hb,ub⟩ := unique_face hJ hr hr'
  exact ⟨(a,b),⟨ha,hb⟩,fun (x,y) h => Prod.ext (ua x h.1) (ub y h.2)⟩

noncomputable abbrev place (hH : H.IsBlockDesign 3 (q+1)) (hJ : J.IsBlockDesign 3 (q+1)) (a : Face H)
    (b : Face J) := gridMap (label hH a) (label hJ b)

private theorem map_label_subset {W : Type*} [DecidableEq W] {H' : Finset (Finset (Option W))}
      (h : H'.IsBlockDesign 3 (q+1)) (c : Face H') (S : Finset (Fin ((kind c).width q))) :
      S.map (label h c)⊆support c := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := mem_map.mp hx
  exact (range_label h c _).mp ⟨i,rfl⟩

theorem belongs_place (hH : H.IsBlockDesign 3 (q+1)) (hJ : J.IsBlockDesign 3 (q+1))
    (a : Face H) (b : Face J) (T : Finset (Grid (Fin ((kind a).width q)) (Fin ((kind b).width q)))) :
    belongs a b (T.map (place hH hJ a b)) ↔ localEvent (kind a) (kind b) T := by
  obtain ⟨hu,hv⟩ := traces_map (label hH a) (label hJ b) T
  simp only [belongs,fits,localEvent,place,hu,hv,card_map]
  exact ⟨fun h => ⟨h.1.2,h.2.2⟩,fun h => ⟨⟨map_label_subset hH a _,h.1⟩,⟨map_label_subset hJ b _,h.2⟩⟩⟩

theorem in_place (hH : H.IsBlockDesign 3 (q+1)) (hJ : J.IsBlockDesign 3 (q+1))
    {a : Face H} {b : Face J} {T : Finset (Grid U V)} (ht : belongs a b T) :
    ∃ S, Finset.map (place hH hJ a b) S=T := by
  classical
  suffices hs : T⊆univ.image (place hH hJ a b) by
    obtain ⟨S,_,he⟩ := subset_image_iff.mp hs
    exact ⟨S,(map_eq_image _ _).trans he⟩
  intro z hz
  cases z with
  | none => exact mem_image.mpr ⟨none,mem_univ _,rfl⟩
  | some p =>
    have h := mem_eraseNone.mpr hz
    obtain ⟨i,hi⟩ := (range_label hH a p.1).mpr (ht.1.1 (mem_image_of_mem _ h))
    obtain ⟨j,hj⟩ := (range_label hJ b p.2).mpr (ht.2.1 (mem_image_of_mem _ h))
    exact mem_image.mpr ⟨some (i,j),mem_univ _,congrArg some (Prod.ext hi hj)⟩

#print axioms traces_map
#print axioms traces_size
#print axioms unique_pair
#print axioms belongs_place
#print axioms in_place
end Erdos722.PointedProduct
