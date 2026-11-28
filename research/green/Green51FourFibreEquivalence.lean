import Green51FourFibreSignature
import Green51AffineRowRestriction
import Green51AffineFrameRecognition

/-! # Recognition of the complete four-point row signature by affine maps -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51OriginRecovery
open scoped Classical
variable {P V : Type*} [AddCommGroup P] [Module F P] [Fintype P] [DecidableEq P]
  [AddCommGroup V] [Module F V] [DecidableEq V]

/-- Above the half-carrier threshold with a two-row margin, the autocorrelation of the mask
recognizes a horizontal direction even when the row contents are arbitrary. -/
theorem horizontal_lag {C D : Finset V} (m : ShortestOddCircuit D C) (row : V→Finset P)
    (large : Fintype.card P*C.card+2*Fintype.card P < 2*(layers C row).card) (z : P×V) :
    z.2=0 ↔ 2*Fintype.card P < lag (layers C row) z := by
  classical
  let M := layers C row
  let U := (univ : Finset P) ×ˢ C
  have inside : M⊆U := by
    rintro ⟨p,i⟩ h
    exact mem_product.mpr ⟨mem_univ _,((mem_layers ..).mp h).1⟩
  constructor
  · intro flat
    have lb := lag_lower inside z (by
      rintro ⟨p,i⟩ h
      apply mem_product.mpr
      exact ⟨mem_univ _,by change i+z.2∈C;rw [flat,add_zero];exact ((mem_layers ..).mp h).1⟩)
    have sz : U.card=Fintype.card P*C.card := by simp [U]
    change _ < lag M z
    change _ < 2*M.card at large
    omega
  · contrapose!
    intro nz
    let J := C.filter fun i => i+z.2∈C
    have sub : (M.filter fun x => x+z∈M) ⊆ (univ : Finset P) ×ˢ J := by
      rintro ⟨p,i⟩ h
      obtain ⟨hx,ht⟩ := mem_filter.mp h
      change (p+z.1,i+z.2)∈layers C row at ht
      exact mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨((mem_layers ..).mp hx).1,((mem_layers ..).mp ht).1⟩⟩
    calc
      lag M z ≤ _ := card_le_card sub
      _ = Fintype.card P*J.card := by simp
      _ ≤ _ := by simpa only [Nat.mul_comm 2 _] using Nat.mul_le_mul_left (Fintype.card P) (circuit_shift_overlap m z.2 nz)

variable {W : Type*} [AddCommGroup W] [Module F W] [DecidableEq W]

/-- Complete test for affine equivalence of two dense masks in four-point circuit frames. -/
theorem four_fibre_equivalence {C D : Finset V} {B E : Finset W}
    (m : ShortestOddCircuit D C) (n : ShortestOddCircuit E B)
    (left : Submodule.span F (C : Set V)=⊤) (right : Submodule.span F (B : Set W)=⊤)
    (row : V→Finset Four) (target : W→Finset Four)
    (occupied : ∀ i∈C,(row i).Nonempty) (occupied' : ∀ i∈B,(target i).Nonempty)
    (large : 4*C.card+8 < 2*(layers C row).card) (large' : 4*B.card+8 < 2*(layers B target).card) :
    (∃ (e : (Four×V) ≃ₗ[F] (Four×W)) (b : Four×W),
      (layers C row).image (fun z => e z+b)=layers B target) ↔
    ∃ (σ : ↥C ≃ ↥B) (u : Four ≃ₗ[F] Four), ∀ i : C,
      (row i.val).card=(target (σ i).val).card ∧
      ((row i.val).card=2 → u (∑ x∈row i.val,x)=∑ y∈target (σ i).val,y) := by
  classical
  constructor
  · rintro ⟨e,b,eq⟩
    have four : Fintype.card Four=4 := by decide
    have a := horizontal_lag m row (by simpa only [four] using large)
    have c := horizontal_lag n target (by simpa only [four] using large')
    have img : Green51OriginRecovery.translate ((layers C row).map e.toEquiv.toEmbedding) b=layers B target := by
      rw [Green51OriginRecovery.translate,map_eq_image,map_eq_image,image_image]
      exact eq
    have horiz (t : Four×V) : t.2=0 ↔ (e t).2=0 := by
      rw [a,c,←img,Green51OriginRecovery.translate,lag_shift,lag_linear]
    obtain ⟨σ,u,off⟩ := rows_of_affine_map C B row target occupied occupied' e b horiz eq
    exact ⟨σ,u,fun i => (moved_fibre_types _ _ u).mp (off i)⟩
  · rintro ⟨σ,u,shape⟩
    obtain ⟨e,b,eq⟩ := four_signature_suffices m n left right σ u row target shape
    exact ⟨e,(b,0),eq⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.horizontal_lag
#print axioms Green51FrameIsomorphisms.four_fibre_equivalence
