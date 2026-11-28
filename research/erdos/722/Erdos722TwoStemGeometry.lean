import Erdos722RectangleCovers
import Erdos722PointedDesignProduct

/-!
# Inflating a pointed triple design over two common stem points

Collapse each finite fiber to its master point and discard both stems.
The one, two or three remaining coordinates determine a unique master
face. Local covers indexed by these faces glue to an ordinary design.
-/

namespace Erdos722.TwoStem
open Finset Function PointedProduct
noncomputable section

abbrev Space (U V : Type*) := Option (Grid U V)

def trace {U V : Type*} [DecidableEq U] (T : Finset (Space U V)) : Finset U := leftTrace T.eraseNone

theorem mem_trace {U V : Type*} [DecidableEq U] {T : Finset (Space U V)} {x : U} :
    x∈trace T ↔ ∃ y, some (some (x,y))∈T := by simp only [trace,mem_leftTrace,mem_eraseNone]

def embed {A B U V : Type*} (e : A ↪ U) (f : B ↪ V) : Space A B ↪ Space U V :=
  (gridMap e f).optionMap

private theorem erase_map {A B : Type*} (e : A ↪ B) (T : Finset (Option A)) :
    (T.map e.optionMap).eraseNone=T.eraseNone.map e := by
  ext b
  constructor
  · intro h
    obtain ⟨(_|a),ha,he⟩ := mem_map.mp (mem_eraseNone.mp h)
    · cases he
    · exact mem_map.mpr ⟨a,mem_eraseNone.mpr ha,Option.some.inj he⟩
  · intro h
    obtain ⟨a,ha,rfl⟩ := mem_map.mp h
    exact mem_eraseNone.mpr (mem_map.mpr ⟨some a,mem_eraseNone.mp ha,rfl⟩)

theorem trace_map {A B U V : Type*} [DecidableEq A] [DecidableEq U]
    (e : A ↪ U) (f : B ↪ V) (T : Finset (Space A B)) :
    trace (T.map (embed e f))=(trace T).map e := by
  classical
  rw [trace,embed,erase_map]
  exact (traces_map e f T.eraseNone).1

private theorem erase_lower {A : Type*} (S : Finset (Option A)) : S.card≤S.eraseNone.card+1 := by
  classical
  by_cases hn : none∈S
  · rw [card_eraseNone_of_mem hn]; omega
  · rw [card_eraseNone_of_not_mem hn]; omega

theorem trace_bounds {U V : Type*} [DecidableEq U] {T : Finset (Space U V)} (hT : T.card=3) :
    0<(trace T).card ∧ (trace T).card≤3 := by
  classical
  have lo := erase_lower T
  have lo' := erase_lower T.eraseNone
  have pos : 0<T.eraseNone.eraseNone.card := by omega
  exact ⟨card_pos.mpr ((card_pos.mp pos).image _),
    card_image_le.trans ((card_eraseNone_le _).trans ((card_eraseNone_le T).trans hT.le))⟩

abbrev Template (k : ℕ) (s : Shape) (U V : Type*) [DecidableEq U] :=
  TripleCover k (fun T : Finset (Space U V) => s.accepts (trace T).card)

def Template.relabel {k s} {A B U V : Type*} [DecidableEq A] [DecidableEq U]
    (C : Template k s A B) (e : A ≃ U) (f : B ≃ V) : Template k s U V := by
  let g := (e.prodCongr f).optionCongr.optionCongr
  apply TripleCover.relabel C g
  intro T
  change s.accepts (trace (T.map (embed e.toEmbedding f.toEmbedding))).card ↔ _
  rw [trace_map,card_map]

abbrev Filling (q : ℕ) (s : Shape) (V : Type*) :=
  Template (q+1) s (Fin (s.width q)) V

variable {U V : Type*} [DecidableEq U] {q : ℕ} {H : Finset (Finset (Option U))}

private noncomputable abbrev place (hH : H.IsBlockDesign 3 (q+1)) (a : Face H) :=
  embed (label hH a) (Embedding.refl V)

private theorem placed_event (hH : H.IsBlockDesign 3 (q+1)) (a : Face H)
    (S : Finset (Space (Fin ((kind a).width q)) V)) :
    fits a (trace (S.map (place hH a))) ↔ (kind a).accepts (trace S).card := by
  rw [fits,place,trace_map,card_map]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  intro x hx
  obtain ⟨i,_,rfl⟩ := mem_map.mp hx
  exact (range_label hH a _).mp ⟨i,rfl⟩

private theorem pull {A X : Type*} (e : A ↪ X) {T : Finset X} {B : Finset A} (h : T⊆B.map e) :
    ∃ S⊆B, S.map e=T := by
  classical
  rw [map_eq_image] at h
  obtain ⟨S,hS,he⟩ := subset_image_iff.mp h
  exact ⟨S,hS,(map_eq_image _ _).trans he⟩

private theorem lifts [Fintype V] (hH : H.IsBlockDesign 3 (q+1)) {a : Face H}
    {T : Finset (Space U V)} (h : fits a (trace T)) : ∃ S, Finset.map (place hH a) S=T := by
  classical
  suffices hs : T⊆univ.map (place hH a) by
    obtain ⟨S,_,he⟩ := pull _ hs
    exact ⟨S,he⟩
  intro z hz
  cases z with
  | none => exact mem_map.mpr ⟨none,mem_univ _,rfl⟩
  | some z =>
    cases z with
    | none => exact mem_map.mpr ⟨some none,mem_univ _,rfl⟩
    | some xy =>
      obtain ⟨i,hi⟩ := (range_label hH a xy.1).mpr (h.1 (mem_trace.mpr ⟨xy.2,hz⟩))
      exact mem_map.mpr ⟨some (some (i,xy.2)),mem_univ _,congrArg some (congrArg some (Prod.ext hi rfl))⟩

theorem inflate [Fintype U] [Fintype V] (hH : H.IsBlockDesign 3 (q+1)) (fill : ∀ s, Filling q s V) :
    ∃ G : Finset (Finset (Space U V)), G.IsBlockDesign 3 (q+1) := by
  classical
  let G : Finset (Finset (Space U V)) := univ.filter fun C =>
    ∃ a : Face H, ∃ B∈(fill (kind a)).blocks, B.map (place hH a)=C
  have memG (C) : C∈G ↔ ∃ a : Face H, ∃ B∈(fill (kind a)).blocks, B.map (place hH a)=C := by simp [G]
  refine ⟨G,?_,?_⟩
  · intro C hC
    obtain ⟨a,B,hB,rfl⟩ := (memG _).mp hC
    simpa using (fill (kind a)).size B hB
  · intro T hT
    obtain ⟨hp,hu⟩ := trace_bounds hT
    obtain ⟨a,ha,ua⟩ := unique_face hH hp hu
    obtain ⟨S,he⟩ := lifts hH ha
    have hc : S.card=3 := by simpa only [← he,card_map] using hT
    obtain ⟨B,⟨hB,hSB⟩,ub⟩ := (fill (kind a)).cover S hc ((placed_event hH a S).mp (he.symm ▸ ha))
    refine ⟨B.map (place hH a),⟨(memG _).mpr ⟨a,B,hB,rfl⟩,he ▸ map_subset_map.mpr hSB⟩,?_⟩
    rintro C ⟨hC,hTC⟩
    obtain ⟨b,D,hD,rfl⟩ := (memG _).mp hC
    obtain ⟨R,hR,hRT⟩ := pull _ hTC
    have hb : fits b (trace T) := hRT ▸ (placed_event hH b R).mpr
      ((fill (kind b)).inside D hD R hR (by simpa only [← hRT,card_map] using hT))
    obtain rfl := ua b hb
    exact congrArg (Finset.map _) (ub D ⟨hD,map_subset_map.mp (he.symm ▸ hTC)⟩)

/-- The two-stem inflation has q+1 points per block and two common stems
in addition to the v times m ordinary points. -/
theorem order_inflate {v m q : ℕ} (fill : ∀ s, Filling q s (Fin m)) (master : ExistsDesign q (v+1)) :
    ExistsDesign q (v*m+2) := by
  classical
  obtain ⟨H,hH⟩ := master
  let e := (Fintype.equivFinOfCardEq (by simp : Fintype.card (Option (Fin v))=v+1)).symm
  obtain ⟨G,hG⟩ := inflate (relabel_design e hH) fill
  let g := Fintype.equivFinOfCardEq (by simp [Space,Grid,Nat.add_assoc] :
    Fintype.card (Space (Fin v) (Fin m))=v*m+2)
  exact ⟨_,relabel_design g hG⟩

#print axioms trace_map
#print axioms trace_bounds
#print axioms inflate
#print axioms order_inflate
end
end Erdos722.TwoStem
