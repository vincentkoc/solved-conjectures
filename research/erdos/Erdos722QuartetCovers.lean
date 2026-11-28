import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-!
# Pair decompositions for the four-point block construction

A partial pair design covers a prescribed relation exactly once. Relabelling
and unions along a partition of the pairs preserve exact coverage.
-/

namespace Erdos722.Quartet
open Finset

abbrev AllPairs (V : Type*) := fun (_ _ : V) => True

/-- Every eligible pair lies in one block, and every pair in a block is eligible. -/
structure Cover (V : Type*) (R : V → V → Prop) (sizes : ℕ → Prop) where
  blocks : Set (Finset V)
  size : ∀ B ∈ blocks, sizes B.card
  sound : ∀ B ∈ blocks, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → R x y
  through : ∀ x y, x ≠ y → R x y → ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

variable {V W I : Type*} {R R' : V → V → Prop} {s t : ℕ → Prop}

def Cover.change (C : Cover V R s) (h : ∀ x y, x ≠ y → (R x y ↔ R' x y))
    (hs : ∀ n, s n → t n) : Cover V R' t where
  blocks := C.blocks
  size B hb := hs _ (C.size B hb)
  sound B hb x hx y hy hxy := (h x y hxy).mp (C.sound B hb x hx y hy hxy)
  through x y hxy hR := C.through x y hxy ((h x y hxy).mpr hR)

def imageRelation (e : W ↪ V) (P : W → W → Prop) (x y : V) : Prop :=
  ∃ a b, e a = x ∧ e b = y ∧ P a b

def Cover.map {P : W → W → Prop} (C : Cover W P s) (e : W ↪ V) :
    Cover V (imageRelation e P) s where
  blocks := (Finset.map e) '' C.blocks
  size := by rintro _ ⟨B,hB,rfl⟩; simpa using C.size B hB
  sound := by
    rintro _ ⟨B,hB,rfl⟩ x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨a,b,rfl,rfl,C.sound B hB a ha b hb (fun he => hxy (congrArg e he))⟩
  through := by
    rintro _ _ hxy ⟨a,b,rfl,rfl,hP⟩
    obtain ⟨B,⟨hB,ha,hb⟩,hu⟩ := C.through a b (fun he => hxy (congrArg e he)) hP
    refine ⟨B.map e,⟨⟨B,hB,rfl⟩,mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩⟩,?_⟩
    rintro _ ⟨⟨T,hT,rfl⟩,hx,hy⟩
    exact congrArg (Finset.map e) (hu T ⟨hT,by simpa using hx,by simpa using hy⟩)

def Cover.relabel (C : Cover W (AllPairs W) s) (e : W ≃ V) : Cover V (AllPairs V) s :=
  (C.map e.toEmbedding).change (fun x y _ => ⟨fun _ => trivial,fun _ =>
    ⟨e.symm x,e.symm y,e.apply_symm_apply _,e.apply_symm_apply _,trivial⟩⟩) (fun _ => id)

/-- Assemble designs whose eligibility relations partition the required pairs. -/
def Cover.assemble {P : I → V → V → Prop} (C : ∀ i, Cover V (P i) s)
    (inside : ∀ i x y, x ≠ y → P i x y → R x y)
    (partition : ∀ x y, x ≠ y → R x y → ∃! i, P i x y) : Cover V R s where
  blocks := {B | ∃ i, B ∈ (C i).blocks}
  size := by rintro B ⟨i,hB⟩; exact (C i).size B hB
  sound := by rintro B ⟨i,hB⟩ x hx y hy hxy; exact inside i x y hxy ((C i).sound B hB x hx y hy hxy)
  through := by
    intro x y hxy hR
    obtain ⟨i,hi,hu⟩ := partition x y hxy hR
    obtain ⟨B,⟨hB,hx,hy⟩,hv⟩ := (C i).through x y hxy hi
    refine ⟨B,⟨⟨i,hB⟩,hx,hy⟩,?_⟩
    rintro A ⟨⟨j,hA⟩,ha,hb⟩
    have he := hu j ((C j).sound A hA x ha y hb hxy)
    subst j
    exact hv A ⟨hA,ha,hb⟩

def Cover.empty (h : ∀ x y : V, x ≠ y → ¬ R x y) : Cover V R s where
  blocks := ∅
  size _ hb := hb.elim
  sound _ hb := hb.elim
  through x y hxy hr := (h x y hxy hr).elim

def Cover.single (B : Finset V) (hB : s B.card) : Cover V (fun x y => x ∈ B ∧ y ∈ B) s where
  blocks := {B}
  size := by rintro _ (rfl : _ = B); exact hB
  sound := by rintro _ (rfl : _ = B) _ hx _ hy _; exact ⟨hx,hy⟩
  through := by rintro x y _ ⟨hx,hy⟩; exact ⟨B,⟨rfl,hx,hy⟩,fun _ h => h.1⟩


/-- Extract a cover from a block parametrisation with one parameter per eligible pair. -/
def Cover.ofLines (L : I → Finset V) (hs : ∀ i, s (L i).card)
    (hr : ∀ i x, x ∈ L i → ∀ y, y ∈ L i → x ≠ y → R x y)
    (hu : ∀ x y, x ≠ y → R x y → ∃! i, x ∈ L i ∧ y ∈ L i) : Cover V R s where
  blocks := Set.range L
  size := by rintro _ ⟨i,rfl⟩; exact hs i
  sound := by rintro _ ⟨i,rfl⟩; exact hr i
  through := by
    intro x y hxy h
    obtain ⟨i,⟨hx,hy⟩,hi⟩ := hu x y hxy h
    exact ⟨L i,⟨⟨i,rfl⟩,hx,hy⟩,by rintro _ ⟨⟨j,rfl⟩,ha,hb⟩; exact congrArg L (hi j ⟨ha,hb⟩)⟩

def inGroup (tag : V → Option I) (i : I) (x : V) := tag x = some i ∨ tag x = none

def cross (tag : V → Option I) (x y : V) :=
  ∃ i j, tag x = some i ∧ tag y = some j ∧ i ≠ j

/-- Fill each group separately. One exceptional point may belong to every group. -/
def Cover.fill (tag : V → Option I) (h0 : ∀ x y, tag x = none → tag y = none → x = y)
    (between : Cover V (cross tag) s)
    (within : ∀ i, Cover V (fun x y => inGroup tag i x ∧ inGroup tag i y) s) :
    Cover V (AllPairs V) s := by
  let P : Option I → V → V → Prop := fun o => match o with
    | none => cross tag
    | some i => fun x y => inGroup tag i x ∧ inGroup tag i y
  apply Cover.assemble (P := P) (fun o => match o with | none => between | some i => within i)
    (fun _ _ _ _ _ => trivial)
  intro x y hxy _
  cases hx : tag x with
  | none =>
    cases hy : tag y with
    | none => exact (hxy (h0 x y hx hy)).elim
    | some j =>
      refine ⟨some j, by simp [P,inGroup,hx,hy], ?_⟩
      rintro (_ | i) hi <;> simp_all [P,inGroup,cross]
  | some i =>
    cases hy : tag y with
    | none =>
      refine ⟨some i, by simp [P,inGroup,hx,hy], ?_⟩
      rintro (_ | j) hj <;> simp_all [P,inGroup,cross]
    | some j =>
      by_cases hij : i = j
      · subst j
        refine ⟨some i, by simp [P,inGroup,hx,hy], ?_⟩
        rintro (_ | j) hj <;> simp_all [P,inGroup,cross]
      · refine ⟨none, by simpa [P,cross,hx,hy], ?_⟩
        rintro (_ | k) hk <;> simp_all [P,inGroup,cross]

/-- An injective local filling may be used on precisely its image. -/
def Cover.fillImage (C : Cover W (AllPairs W) s) (e : W ↪ V) (A : V → Prop)
    (h : ∀ x, (∃ w, e w = x) ↔ A x) : Cover V (fun x y => A x ∧ A y) s :=
  (C.map e).change (by
    intro x y _
    exact ⟨fun ⟨a,b,ha,hb,_⟩ => ⟨(h _).mp ⟨a,ha⟩,(h _).mp ⟨b,hb⟩⟩,by
      rintro ⟨hx,hy⟩
      obtain ⟨a,ha⟩ := (h _).mpr hx
      obtain ⟨b,hb⟩ := (h _).mpr hy
      exact ⟨a,b,ha,hb,trivial⟩⟩) (fun _ => id)


/-- Fill the fibers of a map; the remaining pairs form the transversal part. -/
def Cover.fillFibers (col : V → I) (between : Cover V (fun x y => col x ≠ col y) s)
    (within : ∀ i, Cover {x // col x = i} (AllPairs _) s) : Cover V (AllPairs V) s := by
  let tag := fun x => some (col x)
  apply Cover.fill tag (by simp [tag])
  · exact between.change (by simp [cross,tag]) (fun _ => id)
  · intro i
    apply (within i).fillImage (Function.Embedding.subtype _)
    intro x
    change (∃ w : {z // col z = i}, w.val = x) ↔ some (col x) = some i ∨ some (col x) = none
    simp

/-- Fill the fibers after adjoining a single point shared by all groups. -/
def Cover.adjoin (col : V → I) (between : Cover V (fun x y => col x ≠ col y) s)
    (within : ∀ i, Cover (Option {x // col x = i}) (AllPairs _) s) :
    Cover (Option V) (AllPairs _) s := by
  let tag := Option.map col
  apply Cover.fill tag (by rintro (_ | x) (_ | y) <;> simp [tag])
  · apply (between.map Function.Embedding.some).change _ (fun _ => id)
    rintro (_ | x) (_ | y) _ <;> simp [imageRelation,cross,tag,Function.Embedding.some]
  · intro i
    apply (within i).fillImage (Function.Embedding.subtype _).optionMap
    rintro (_ | x)
    · exact ⟨fun _ => Or.inr rfl,fun _ => ⟨none,rfl⟩⟩
    · constructor
      · rintro ⟨(_ | ⟨y,hy⟩),he⟩
        · contradiction
        · change some y = some x at he
          exact Or.inl (congrArg some ((congrArg col (Option.some.inj he)).symm.trans hy))
      · rintro (h | h)
        · exact ⟨some ⟨x,Option.some.inj h⟩,rfl⟩
        · contradiction

/-- Convert to the exact upstream pair-design predicate. -/
theorem Cover.design [Fintype V] {k : ℕ} (C : Cover V (AllPairs V) (· = k)) :
    ∃ H : Finset (Finset V), H.IsBlockDesign 2 k := by
  classical
  let H := univ.filter (· ∈ C.blocks)
  refine ⟨H,fun B hB => C.size B (mem_filter.mp hB).2,?_⟩
  intro S hS
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hS
  simpa only [H,mem_filter,mem_univ,true_and,insert_subset_iff,singleton_subset_iff,and_assoc]
    using C.through x y hxy trivial

def Cover.ofDesign {H : Finset (Finset V)} {k : ℕ} (hH : H.IsBlockDesign 2 k) :
    Cover V (AllPairs V) (· = k) where
  blocks := ↑H
  size := hH.1
  sound _ _ _ _ _ _ _ := trivial
  through x y hxy _ := by
    classical
    simpa only [Finset.mem_coe,insert_subset_iff,singleton_subset_iff,and_assoc]
      using hH.2 {x,y} (card_pair hxy)


/-- Existence on the canonical labelled finite vertex set. -/
def Has (s : ℕ → Prop) (n : ℕ) := Nonempty (Cover (Fin n) (AllPairs _) s)

noncomputable def Has.realize {n : ℕ} (h : Has s n) [Fintype V] (hc : Fintype.card V = n) :
    Cover V (AllPairs _) s := h.some.relabel (Fintype.equivFinOfCardEq hc).symm

theorem Cover.has [Fintype V] {n : ℕ} (C : Cover V (AllPairs _) s) (hc : Fintype.card V = n) :
    Has s n := ⟨C.relabel (Fintype.equivFinOfCardEq hc)⟩

theorem Has.mono {n : ℕ} (h : Has s n) (hs : ∀ k, s k → t k) : Has t n :=
  ⟨h.some.change (fun _ _ _ => Iff.rfl) hs⟩

theorem Has.single {n : ℕ} (h : s n) : Has s n := by
  classical
  have hs : s (univ : Finset (Fin n)).card := by simpa using h
  exact ⟨(Cover.single univ hs).change (by simp [AllPairs]) (fun _ => id)⟩

#print axioms Cover.assemble
#print axioms Cover.design

end Erdos722.Quartet
