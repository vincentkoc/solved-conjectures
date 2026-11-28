import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.EquivFin

/-!
# Pointed faces of a Steiner triple design

Distinguish a point at infinity. One finite coordinate selects its point,
two select the block through infinity, and three select their unique block.
This partitions projections of triples in a product of two pointed designs.
-/

namespace Erdos722.PointedProduct
open Finset
open Function

inductive Shape
  | point | line | circle
  deriving DecidableEq

def Shape.width (q : ℕ) : Shape → ℕ
  | .point => 1
  | .line => q
  | .circle => q+1

def Shape.accepts : Shape → ℕ → Prop
  | .point, n => n=1
  | .line, n => 2≤n
  | .circle, n => n=3

instance (s : Shape) (n : ℕ) : Decidable (s.accepts n) := by
  cases s <;> unfold Shape.accepts <;> infer_instance

variable {U : Type*} [DecidableEq U]

abbrev Face (H : Finset (Finset (Option U))) := U ⊕ {B // B∈H}

def kind {H : Finset (Finset (Option U))} : Face H → Shape
  | .inl _ => .point
  | .inr B => if none∈B.val then .line else .circle

def support {H : Finset (Finset (Option U))} : Face H → Finset U
  | .inl x => {x}
  | .inr B => B.val.eraseNone

def fits {H : Finset (Finset (Option U))} (f : Face H) (P : Finset U) : Prop :=
  P⊆support f ∧ (kind f).accepts P.card

omit [DecidableEq U] in
private theorem subset_some {P : Finset U} {B : Finset (Option U)} :
    P.map Embedding.some ⊆ B ↔ P⊆B.eraseNone := by
  constructor
  · intro h x hx
    exact mem_eraseNone.mpr (h (mem_map.mpr ⟨x,hx,rfl⟩))
  · intro h x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact mem_eraseNone.mp (h hy)

private theorem singleton_case {H : Finset (Finset (Option U))} {x : U} :
    ∃! f : Face H, fits f {x} := by
  refine ⟨.inl x,⟨Subset.rfl,by simp [kind,Shape.accepts]⟩,?_⟩
  rintro (y | B) ⟨hP,hs⟩
  · have he : x=y := by simpa [support] using (hP (mem_singleton_self x) : x∈support (H:=H) (.inl y))
    exact congrArg Sum.inl he.symm
  · by_cases h : none∈B.val <;> simp [kind,h,Shape.accepts] at hs

private theorem pair_case {H : Finset (Finset (Option U))} {q : ℕ}
    (hH : H.IsBlockDesign 3 (q+1)) {P : Finset U} (hP : P.card=2) :
    ∃! f : Face H, fits f P := by
  let T := insert none (P.map Embedding.some)
  have hn : none ∉ P.map Embedding.some := by simp
  have hT : T.card=3 := by simp [T,hn,hP]
  obtain ⟨B,⟨hB,hTB⟩,uniq⟩ := hH.2 T hT
  have hInf : none∈B := hTB (mem_insert_self _ _)
  refine ⟨.inr ⟨B,hB⟩,⟨subset_some.mp ((subset_insert _ _).trans hTB),?_⟩,?_⟩
  · simp [kind,hInf,Shape.accepts,hP]
  · rintro (x | C) ⟨hc,hs⟩
    · simp [kind,Shape.accepts,hP] at hs
    · by_cases h : none∈C.val
      · exact congrArg Sum.inr (Subtype.ext (uniq C.val ⟨C.property,insert_subset h (subset_some.mpr hc)⟩))
      · simp [kind,h,Shape.accepts,hP] at hs

private theorem triple_case {H : Finset (Finset (Option U))} {q : ℕ}
    (hH : H.IsBlockDesign 3 (q+1)) {P : Finset U} (hP : P.card=3) :
    ∃! f : Face H, fits f P := by
  obtain ⟨B,⟨hB,hPB⟩,uniq⟩ := hH.2 (P.map Embedding.some) (by simpa using hP)
  refine ⟨.inr ⟨B,hB⟩,⟨subset_some.mp hPB,?_⟩,?_⟩
  · by_cases h : none∈B <;> simp [kind,h,Shape.accepts,hP]
  · rintro (x | C) ⟨hc,hs⟩
    · simp [kind,Shape.accepts,hP] at hs
    · exact congrArg Sum.inr (Subtype.ext (uniq C.val ⟨C.property,subset_some.mpr hc⟩))

/-- Every projection of one, two or three finite coordinates selects a unique face. -/
theorem unique_face {H : Finset (Finset (Option U))} {q : ℕ}
    (hH : H.IsBlockDesign 3 (q+1)) {P : Finset U} (hp : 0<P.card) (ht : P.card≤3) :
    ∃! f : Face H, fits f P := by
  have hc : P.card=1 ∨ P.card=2 ∨ P.card=3 := by omega
  rcases hc with h | h | h
  · obtain ⟨x,rfl⟩ := card_eq_one.mp h
    exact singleton_case
  · exact pair_case hH h
  · exact triple_case hH h

theorem support_size {H : Finset (Finset (Option U))} {q : ℕ}
    (hH : H.IsBlockDesign 3 (q+1)) (f : Face H) : (support f).card=(kind f).width q := by
  rcases f with x | ⟨B,hB⟩
  · simp [support,kind,Shape.width]
  · have h := hH.1 B hB
    by_cases hn : none∈B
    · simp [support,kind,hn,Shape.width,card_eraseNone_of_mem hn,h]
    · simp [support,kind,hn,Shape.width,card_eraseNone_of_not_mem hn,h]

noncomputable def label {H : Finset (Finset (Option U))} {q : ℕ}
    (hH : H.IsBlockDesign 3 (q+1)) (f : Face H) : Fin ((kind f).width q) ↪ U :=
  ((Fintype.equivFinOfCardEq (by simpa using support_size hH f : Fintype.card (support f) =
    (kind f).width q)).symm.toEmbedding).trans (Embedding.subtype _)

theorem range_label {H : Finset (Finset (Option U))} {q : ℕ}
    (hH : H.IsBlockDesign 3 (q+1)) (f : Face H) (x : U) :
    (∃ i, label hH f i=x) ↔ x∈support f := by
  let e := Fintype.equivFinOfCardEq (by simpa using support_size hH f :
    Fintype.card (support f)=(kind f).width q)
  constructor
  · rintro ⟨i,rfl⟩
    exact (e.symm i).property
  · intro hx
    exact ⟨e ⟨x,hx⟩,Subtype.ext_iff.mp (e.symm_apply_apply ⟨x,hx⟩)⟩

#print axioms unique_face
#print axioms support_size
#print axioms range_label
end Erdos722.PointedProduct
