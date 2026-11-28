import Green51FibrePresentations
import Green51ArbitraryFibreEquivalence

/-! # Affine equivalence of dense doubles with arbitrary binary fibre dimension -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51OriginRecovery Green51MissingMasks Green51Hyperplane
open scoped Classical

/-- Compare the row translation classes after allowing a single linear change of fibre
coordinates, common to all rows. -/
def FibreMatch {V H : Type*} [AddCommGroup H] [Module F H] [DecidableEq H] [Fintype H]
    (B : Finset V) (row target : V → Finset H) : Prop :=
  ∃ u : H ≃ₗ[F] H, ∀ t : Finset (Finset H),
    frequency (fun i : B => translationClass ((row i.val).map u.toEquiv.toEmbedding)) t =
      frequency (fun i : B => translationClass (target i.val)) t

theorem presented_fibre_equivalence {s r k : ℕ}
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {B : Finset (𝔽₂ (2*(s+1)))} (ref : ShortestOddCircuit B B) (size : B.card=2*s+3)
    (full : Submodule.span F (B : Set (𝔽₂ (2*(s+1))))=⊤)
    {row target : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r)}
    (live : ∀ i∈B,(row i).Nonempty) (live' : ∀ i∈B,(target i).Nonempty)
    (sz : (layers B row).card=k) (sz' : (layers B target).card=k)
    {S T : Finset (𝔽₂ (2*(s+1)+r))} (a : FibrePresents B row S) (b : FibrePresents B target T) :
    AffineRelated S T ↔ FibreMatch B row target := by
  classical
  obtain ⟨e,he⟩ := a
  obtain ⟨f,hf⟩ := b
  have left := AffineRelated.linear (layers B row) e
  have right := AffineRelated.linear (layers B target) f
  rw [he] at left
  rw [hf] at right
  have slots : Fintype.card (𝔽₂ r)=2^r := by simp [𝔽₂,𝔽]
  have rows := arbitrary_fibre_equivalence ref ref full full row target live live'
    (by rw [slots,size,sz];exact fibre_margin near) (by rw [slots,size,sz'];exact fibre_margin near)
  constructor
  · intro h
    exact rows.mp ((left.trans h.compl).trans right.symm)
  · intro h
    have h' : AffineRelated Sᶜ Tᶜ := (left.symm.trans (rows.mpr h)).trans right
    simpa only [compl_compl] using h'.compl

/-- A complete invariant of the actual near-extremal dense doubles in arbitrary fibre
dimension, together with realization of every occupied word of the required size. -/
theorem dense_double_fibre_classes {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) :
    ∃ B : Finset (𝔽₂ (2*(s+1))), ShortestOddCircuit B B ∧ B.card=2*s+3 ∧
      ∃ row : (countedDoubles (2*(s+1)+r) k (threshold (2*s))) → 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r),
      (∀ S, FibrePresents B (row S) S.val) ∧
      (∀ S T, AffineRelated S.val T.val ↔ FibreMatch B (row S) (row T)) ∧
      ∀ w : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r), (∀ i∈B,(w i).Nonempty) → (layers B w).card=k →
        ∃ S ∈ countedDoubles (2*(s+1)+r) k (threshold (2*s)), FibrePresents B w S := by
  classical
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  choose row live sz presents using fun (S : countedDoubles (2*(s+1)+r) k (threshold (2*s))) =>
    present_counted_fibres hs near ref size full S.property
  exact ⟨B,ref,size,row,presents,fun S T => presented_fibre_equivalence near ref size full
    (live S) (live T) (sz S) (sz T) (presents S) (presents T),realize_fibre_rows hs near ref size full⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.presented_fibre_equivalence
#print axioms Green51FrameIsomorphisms.dense_double_fibre_classes
