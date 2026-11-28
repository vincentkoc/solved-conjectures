import Green51FrameOffsetInterpolation

/-! # Affine changes of coordinates on rows above an odd circuit -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical
variable {P V Q W : Type*} [AddCommGroup P] [Module F P] [AddCommGroup V] [Module F V]
  [AddCommGroup Q] [Module F Q] [AddCommGroup W] [Module F W] [DecidableEq V]

/-- Every permutation between spanning odd circuits extends to a linear equivalence. -/
theorem spanning_circuit_permutation [DecidableEq W] {C D : Finset V} {B E : Finset W}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B)
    (left : Submodule.span F (C : Set V)=⊤) (right : Submodule.span F (B : Set W)=⊤)
    (σ : ↥C ≃ ↥B) : ∃ v : V ≃ₗ[F] W, ∀ i : C, v i.val=(σ i).val := by
  obtain ⟨l,acts⟩ := Green51MissingMasks.circuit_span_equiv m n σ
  let L := Submodule.span F (C : Set V)
  let R := Submodule.span F (B : Set W)
  let inclL : L ≃ₗ[F] V := LinearEquiv.ofBijective L.subtype ⟨Subtype.val_injective,fun x =>
    ⟨⟨x,show x∈L by change x∈Submodule.span F (C : Set V); rw [left]; trivial⟩,rfl⟩⟩
  let inclR : R ≃ₗ[F] W := LinearEquiv.ofBijective R.subtype ⟨Subtype.val_injective,fun x =>
    ⟨⟨x,show x∈R by change x∈Submodule.span F (B : Set W); rw [right]; trivial⟩,rfl⟩⟩
  refine ⟨(inclL.symm.trans l).trans inclR,fun i => ?_⟩
  let x : L := ⟨i.val,Submodule.subset_span i.property⟩
  change inclR (l (inclL.symm (inclL x)))=(σ i).val
  rw [inclL.symm_apply_apply]
  exact acts i

theorem row_maps_extend {C D : Finset V} (m : ShortestOddCircuit D C)
    (u : P ≃ₗ[F] Q) (v : V ≃ₗ[F] W) (offset : V → Q) :
    ∃ e : (P×V) ≃ₗ[F] (Q×W), ∃ b : Q, ∀ i∈C, ∀ p : P,
      e (p,i)+(b,0)=(u p+offset i,v i) := by
  obtain ⟨f,hf⟩ := interpolate_offsets m offset
  let e := ((u.prodCongr (LinearEquiv.refl F V)).trans (shear f)).trans ((LinearEquiv.refl F Q).prodCongr v)
  refine ⟨e,∑ y∈C,offset y,fun i hi p => ?_⟩
  change ((u p+f i)+(∑ y∈C,offset y),v i+0)=(u p+offset i,v i)
  rw [add_assoc,hf i hi,add_zero]

variable [DecidableEq P] [DecidableEq Q] [DecidableEq W]

def layers (C : Finset V) (row : V → Finset P) : Finset (P×V) :=
  C.biUnion (fun i => (row i).image (fun p => (p,i)))

omit [AddCommGroup P] [Module F P] [AddCommGroup V] [Module F V] in
@[simp] theorem mem_layers (C : Finset V) (row : V → Finset P) (p : P) (i : V) :
    (p,i)∈layers C row ↔ i∈C ∧ p∈row i := by simp [layers]

theorem layers_equivalent {C D : Finset V} (m : ShortestOddCircuit D C)
    (u : P ≃ₗ[F] Q) (v : V ≃ₗ[F] W) (offset : V → Q) (row : V → Finset P) (target : W → Finset Q)
    (compat : ∀ i∈C, (row i).image (fun p => u p+offset i)=target (v i)) :
    ∃ e : (P×V) ≃ₗ[F] (Q×W), ∃ b : Q,
      (layers C row).image (fun z => e z+(b,0)) = layers (C.map v.toEquiv.toEmbedding) target := by
  classical
  obtain ⟨e,b,act⟩ := row_maps_extend m u v offset
  refine ⟨e,b,Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨⟨p,i⟩,hp,rfl⟩ := mem_image.mp hz
    obtain ⟨hi,hp⟩ := (mem_layers ..).mp hp
    rw [act i hi p,mem_layers]
    refine ⟨mem_map_of_mem _ hi,?_⟩
    rw [←compat i hi]
    exact mem_image_of_mem _ hp
  · rintro ⟨q,j⟩ hz
    obtain ⟨hj,hq⟩ := (mem_layers ..).mp hz
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hj
    change q∈target (v i) at hq
    rw [←compat i hi] at hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    exact mem_image.mpr ⟨(p,i),(mem_layers ..).mpr ⟨hi,hp⟩,act i hi p⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.spanning_circuit_permutation
#print axioms Green51FrameIsomorphisms.row_maps_extend
#print axioms Green51FrameIsomorphisms.mem_layers
#print axioms Green51FrameIsomorphisms.layers_equivalent
