import Green51DenseAffineClassification
import Mathlib.Data.Multiset.Fintype

/-! # Realizing specified multiplicities of four-point row types -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

/-- Sizes of representative occupied masks of the six translation types. -/
def sizeOfKind : RowKind → ℕ
  | .inl i => ![1,3,4] i
  | .inr _ => 2

theorem occupied_representatives : ∀ k : RowKind, ∃ S : Finset Four, S.Nonempty ∧ kind S=k := by decide +kernel
theorem kind_size : ∀ S : Finset Four, S.Nonempty → sizeOfKind (kind S)=S.card := by decide +kernel

theorem card_layers {V : Type*} [DecidableEq V] (B : Finset V) (S : V→Finset Four) :
    (layers B S).card=∑ i : B,(S i.val).card := by
  classical
  rw [layers,card_biUnion,←sum_attach B]
  · apply sum_congr rfl
    intro i _
    exact card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
  · intro i _ j _ ne
    apply disjoint_left.mpr
    intro x ha hb
    obtain ⟨a,_,rfl⟩ := mem_image.mp ha
    obtain ⟨b,_,eq⟩ := mem_image.mp hb
    exact ne (congrArg Prod.snd eq).symm

/-- Any labelled histogram with the right total is realized by an assignment of kinds. -/
theorem realize_frequencies {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (h : K→ℕ) (sum : ∑ k,h k=Fintype.card I) : ∃ f : I→K,∀ k, frequency f k=h k := by
  classical
  let e : I ≃ (Σ k,Fin (h k)) := Fintype.equivOfCardEq (by simpa using sum.symm)
  refine ⟨fun i => (e i).1,fun k => ?_⟩
  let F : {x : (Σ j, Fin (h j)) // x.1=k} ≃ Fin (h k) := {
    toFun x := Fin.cast (congrArg h x.property) x.val.2
    invFun j := ⟨⟨k,j⟩,rfl⟩
    left_inv := by rintro ⟨⟨_,j⟩,rfl⟩;rfl
    right_inv := fun _ => rfl }
  let lift : {i // (e i).1=k} ≃ {x : (Σ j,Fin (h j)) // x.1=k} := e.subtypeEquiv (fun _ => Iff.rfl)
  simpa [frequency] using Fintype.card_congr (lift.trans F)

/-- Adding a weight at each index equals adding the type weights with their multiplicities. -/
theorem sum_frequencies {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (f : I→K) (w : K→ℕ) : (∑ i,w (f i))=∑ k,frequency f k*w k := by
  classical
  calc
    _ = ∑ z : (Σ k, {i // f i=k}), w (f z.2.val) := ((Equiv.sigmaFiberEquiv f).sum_comp _).symm
    _ = ∑ k,frequency f k*w k := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro k _
      calc
        (∑ x : {i // f i=k}, w (f x.val)) = ∑ _x : {i // f i=k}, w k :=
          sum_congr rfl (fun x _ => congrArg w x.property)
        _ = _ := by simp [frequency]

/-- A labelled inventory occurs on the given reference circuit exactly when it has the required
number of rows and points. The ambient vector space enters only through its circuit labels. -/
theorem inventory_iff {V : Type*} [DecidableEq V] (B : Finset V) (k : ℕ) (h : RowKind→ℕ) :
    (∃ S : V→Finset Four, (∀ i∈B,(S i).Nonempty) ∧ (layers B S).card=k ∧
      ∀ t,frequency (fun i : B => kind (S i.val)) t=h t) ↔
    (∑ t,h t)=B.card ∧ (∑ t,h t*sizeOfKind t)=k := by
  classical
  constructor
  · rintro ⟨S,live,sz,hits⟩
    let f (i : B) := kind (S i.val)
    have n : Fintype.card ↥B=∑ t,frequency f t := by
      simpa using sum_frequencies f (fun _ => 1)
    have w := sum_frequencies f sizeOfKind
    have actual (i : B) : sizeOfKind (f i)=(S i.val).card := kind_size _ (live _ i.property)
    rw [card_layers] at sz
    simp only [actual] at w
    refine ⟨?_,by simpa only [f,hits] using w.symm.trans sz⟩
    calc
      (∑ t,h t)=∑ t,frequency f t := sum_congr rfl (fun t _ => (hits t).symm)
      _ = B.card := by simpa only [Fintype.card_coe] using n.symm
  · rintro ⟨n,w⟩
    obtain ⟨f,counts⟩ := realize_frequencies (I := ↥B) h (by simpa only [Fintype.card_coe] using n)
    choose rep live kind_rep using occupied_representatives
    let S (x : V) := if hx : x∈B then rep (f ⟨x,hx⟩) else ∅
    have atIndex (i : B) : S i.val=rep (f i) := dif_pos i.property
    have labels (i : B) : kind (S i.val)=f i := (congrArg kind (atIndex i)).trans (kind_rep _)
    have occ (x : V) (hx : x∈B) : (S x).Nonempty := by rw [show S x=rep (f ⟨x,hx⟩) from dif_pos hx];exact live _
    refine ⟨S,occ,?_,by simpa only [labels] using counts⟩
    rw [card_layers]
    calc
      _ = ∑ i : B,sizeOfKind (f i) := sum_congr rfl fun i _ =>
        (kind_size _ (occ _ i.property)).symm.trans (congrArg sizeOfKind (labels i))
      _ = _ := by simpa only [counts] using (sum_frequencies f sizeOfKind).trans (by simpa only [counts] using w)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.card_layers
#print axioms Green51FrameIsomorphisms.realize_frequencies
#print axioms Green51FrameIsomorphisms.sum_frequencies

#print axioms Green51FrameIsomorphisms.inventory_iff
