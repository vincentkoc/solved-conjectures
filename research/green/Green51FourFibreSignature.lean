import Green51AffineFrameRows
import Green51FourFibreTypes

/-! # Constructing affine equivalences between masks of a four-point circuit frame -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical
variable {V W : Type*} [AddCommGroup V] [Module F V] [DecidableEq V]
  [AddCommGroup W] [Module F W] [DecidableEq W]

/-- An identification of circuit labels and a single identification of the three pair directions
suffice to construct an ambient affine equivalence of two four-point-fibre masks. -/
theorem four_signature_suffices {C D : Finset V} {B E : Finset W}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B)
    (left : Submodule.span F (C : Set V)=⊤) (right : Submodule.span F (B : Set W)=⊤)
    (σ : ↥C ≃ ↥B) (u : Four ≃ₗ[F] Four) (row : V → Finset Four) (target : W → Finset Four)
    (shape : ∀ i : C, (row i.val).card=(target (σ i).val).card ∧
      ((row i.val).card=2 → u (∑ x∈row i.val,x)=∑ y∈target (σ i).val,y)) :
    ∃ e : (Four×V) ≃ₗ[F] (Four×W), ∃ b : Four,
      (layers C row).image (fun z => e z+(b,0)) = layers B target := by
  classical
  obtain ⟨v,perm⟩ := spanning_circuit_permutation m n left right σ
  have mapC : C.map v.toEquiv.toEmbedding=B := by
    ext j
    constructor
    · rintro h
      obtain ⟨i,hi,rfl⟩ := mem_map.mp h
      change v i∈B
      rw [show v i=(σ ⟨i,hi⟩).val from perm ⟨i,hi⟩]
      exact (σ ⟨i,hi⟩).property
    · intro h
      let x := σ.symm ⟨j,h⟩
      exact mem_map.mpr ⟨x.val,x.property,(perm x).trans (congrArg Subtype.val (σ.apply_symm_apply ⟨j,h⟩))⟩
  choose off hoff using fun i : C => (moved_fibre_types _ _ u).mpr (shape i)
  let offset (i : V) := if hi : i∈C then off ⟨i,hi⟩ else 0
  have compat (i : V) (hi : i∈C) :
      (row i).image (fun p => u p+offset i)=target (v i) := by
    rw [show v i=(σ ⟨i,hi⟩).val from perm ⟨i,hi⟩]
    simpa only [offset,dif_pos hi] using hoff ⟨i,hi⟩
  simpa only [mapC] using layers_equivalent m u v offset row target compat

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.four_signature_suffices
