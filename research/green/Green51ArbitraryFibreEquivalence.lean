import Green51AffineFrameRows
import Green51FourFibreEquivalence
import Green51RowFrequencies
import Green51AffineSetTransport

/-! # Row translation classes for binary circuit frames with arbitrary fibre size -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51OriginRecovery
open scoped Classical
variable {P V W : Type*} [AddCommGroup P] [Module F P] [DecidableEq P] [Fintype P]
  [AddCommGroup V] [Module F V] [DecidableEq V]
  [AddCommGroup W] [Module F W] [DecidableEq W]

omit [Fintype P] in
/-- A common linear identification and independent row translations extend to the full frame. -/
theorem row_identifications_extend {C D : Finset V} {B E : Finset W}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B)
    (left : Submodule.span F (C : Set V)=⊤) (right : Submodule.span F (B : Set W)=⊤)
    (σ : ↥C ≃ ↥B) (u : P ≃ₗ[F] P) (row : V → Finset P) (target : W → Finset P)
    (shape : ∀ i : C, ∃ a : P,(row i.val).image (fun p => u p+a)=target (σ i).val) :
    ∃ e : (P×V) ≃ₗ[F] (P×W), ∃ b : P,
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
  choose off hoff using shape
  let offset (i : V) := if hi : i∈C then off ⟨i,hi⟩ else 0
  have compat (i : V) (hi : i∈C) :
      (row i).image (fun p => u p+offset i)=target (v i) := by
    rw [show v i=(σ ⟨i,hi⟩).val from perm ⟨i,hi⟩]
    simpa only [offset,dif_pos hi] using hoff ⟨i,hi⟩
  simpa only [mapC] using layers_equivalent m u v offset row target compat

private theorem moved_class (u : P ≃ₗ[F] P) (R T : Finset P) :
    translationClass (R.map u.toEquiv.toEmbedding)=translationClass T ↔
      ∃ a : P,R.image (fun p => u p+a)=T := by
  rw [eq_comm,same_class_iff]
  apply exists_congr
  intro a
  simp only [Green51OriginRecovery.translate,map_eq_image,image_image,Function.comp_def]
  rfl

/-- A single linear change of fibre coordinates matches the complete histogram of row
translation classes exactly when the two dense circuit masks are affinely equivalent. -/
theorem arbitrary_fibre_equivalence {C D : Finset V} {B E : Finset W}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B)
    (left : Submodule.span F (C : Set V)=⊤) (right : Submodule.span F (B : Set W)=⊤)
    (row : V→Finset P) (target : W→Finset P)
    (occupied : ∀ i∈C,(row i).Nonempty) (occupied' : ∀ i∈B,(target i).Nonempty)
    (large : Fintype.card P*C.card+2*Fintype.card P < 2*(layers C row).card)
    (large' : Fintype.card P*B.card+2*Fintype.card P < 2*(layers B target).card) :
    AffineRelated (layers C row) (layers B target) ↔
      ∃ u : P ≃ₗ[F] P, ∀ t : Finset (Finset P),
        frequency (fun i : C => translationClass ((row i.val).map u.toEquiv.toEmbedding)) t =
        frequency (fun j : B => translationClass (target j.val)) t := by
  classical
  constructor
  · rintro ⟨e,b,eq⟩
    have img : Green51OriginRecovery.translate ((layers C row).map e.toEquiv.toEmbedding) b=layers B target := by
      rw [Green51OriginRecovery.translate,map_eq_image,map_eq_image,image_image]
      exact eq
    have horizontal (t : P×V) : t.2=0 ↔ (e t).2=0 := by
      rw [horizontal_lag m row large,horizontal_lag n target large',←img,Green51OriginRecovery.translate,lag_shift,lag_linear]
    obtain ⟨σ,u,acts⟩ := rows_of_affine_map C B row target occupied occupied' e b horizontal eq
    exact ⟨u,(match_iff_frequency _ _).mp ⟨σ,fun i => (moved_class u _ _).mpr (acts i)⟩⟩
  · rintro ⟨u,hist⟩
    obtain ⟨σ,matchRows⟩ := (match_iff_frequency _ _).mpr hist
    obtain ⟨e,b,eq⟩ := row_identifications_extend m n left right σ u row target
      (fun i => (moved_class u _ _).mp (matchRows i))
    exact ⟨e,(b,0),eq⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.row_identifications_extend
#print axioms Green51FrameIsomorphisms.arbitrary_fibre_equivalence
