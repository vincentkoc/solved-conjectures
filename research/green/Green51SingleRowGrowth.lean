import Green51UniversalDefectNumber
import Mathlib.Data.Fintype.Powerset

/-! # Single-row configurations give a lower bound for the stable Green 51 class count. -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

private theorem card_le_param {A B G : Type*} [Finite A] [Finite B] [Finite G]
    (f : A → B) (move : G → A → A)
    (same : ∀ x y, f x=f y → ∃ g, move g x=y) :
    Nat.card A ≤ Nat.card B * Nat.card G := by
  classical
  let pick (y : Set.range f) : A := y.property.choose
  have picked (y : Set.range f) : f (pick y)=y.val := y.property.choose_spec
  let onto (p : Set.range f × G) := move p.2 (pick p.1)
  have surj : Function.Surjective onto := by
    intro a
    let y : Set.range f := ⟨f a,⟨a,rfl⟩⟩
    obtain ⟨g,hg⟩ := same (pick y) a (picked y)
    exact ⟨(y,g),hg⟩
  have hh := Nat.card_le_card_of_surjective onto surj
  rw [Nat.card_prod] at hh
  exact hh.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective
    (Subtype.val : Set.range f → B) Subtype.val_injective))

private theorem linear_count (d : ℕ) :
    Nat.card (𝔽₂ d ≃ₗ[F] 𝔽₂ d) ≤ 2^(d*d) := by
  let b := Pi.basisFun F (Fin d)
  let code (u : 𝔽₂ d ≃ₗ[F] 𝔽₂ d) (i : Fin d) := u (b i)
  have inj : Function.Injective code := by
    intro u v e
    have h : u.toLinearMap=v.toLinearMap := b.ext (fun i => congrFun e i)
    exact LinearEquiv.toLinearMap_injective h
  simpa [𝔽₂,𝔽,Nat.card_eq_fintype_card,←pow_mul] using Nat.card_le_card_of_injective code inj

theorem single_row_count {h d : ℕ} (pos : 0<h) (dim : d≤h-1) :
    (2^d).choose h ≤ universalDefectNumber h * 2^(d*d+d) := by
  classical
  let i0 : Fin h := ⟨0,pos⟩
  let word (s : Finset (𝔽₂ d)) (i : Fin h) := if i=i0 then s else ∅
  have sz (s : Finset (𝔽₂ d)) : (∑ i,(word s i).card)=s.card := by simp [word,apply_ite Finset.card]
  obtain ⟨f,hf⟩ := (finrank_le_iff_exists_linearMap (R := F) (M := 𝔽₂ d) (M' := 𝔽₂ (h-1))).mp
    (by simpa [𝔽₂,𝔽] using dim)
  let classify (s : {s : Finset (𝔽₂ d) // s.card=h}) :
      Quotient (wordSetoid (Fin h) (𝔽₂ (h-1)) h) :=
    Quotient.mk _ ⟨fun i => (word s.val i).map ⟨f,hf⟩,by simpa only [card_map,sz] using s.property⟩
  let move (g : (𝔽₂ d ≃ₗ[F] 𝔽₂ d) × 𝔽₂ d) (s : {s : Finset (𝔽₂ d) // s.card=h}) :
      {s : Finset (𝔽₂ d) // s.card=h} :=
    ⟨s.val.map ((g.1.toEquiv.trans (Equiv.addRight g.2)).toEmbedding),by simpa using s.property⟩
  have same (x y) (e : classify x=classify y) : ∃ g,move g x=y := by
    have hmatch := (word_embedding_iff (word x.val) (word y.val) f hf).mp (Quotient.exact e)
    obtain ⟨σ,u,t,hc⟩ := hmatch
    have row := hc i0
    have fixed : σ i0=i0 := by
      by_contra ne
      have := congrArg Finset.card row
      simp [word,ne,x.property] at this
      omega
    exact ⟨(u,t i0),Subtype.ext (by simpa [move,word,fixed] using row)⟩
  let _ : Finite (𝔽₂ d ≃ₗ[F] 𝔽₂ d) := Finite.of_injective (fun u : 𝔽₂ d ≃ₗ[F] 𝔽₂ d => (u : 𝔽₂ d → 𝔽₂ d)) DFunLike.coe_injective
  have hc := card_le_param classify move same
  rw [Nat.card_prod] at hc
  have hs : Nat.card {s : Finset (𝔽₂ d) // s.card=h}=(2^d).choose h := by
    simp [Nat.card_eq_fintype_card,𝔽₂,𝔽]
  rw [hs] at hc
  have hfib : Nat.card (𝔽₂ d)=2^d := by simp [Nat.card_eq_fintype_card,𝔽₂,𝔽]
  rw [hfib] at hc
  exact hc.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _ (linear_count d)).trans_eq (pow_add 2 (d*d) d).symm))

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.single_row_count
