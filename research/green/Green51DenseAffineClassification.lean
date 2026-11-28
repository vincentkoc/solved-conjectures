import Green51DenseFramePresentations
import Green51AffineSetTransport
import Green51RowFrequencies

/-! # Affine classification for the codimension-two near-extremal dense sumsets -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

/-- The occupied row presentations of two dense doubles determine their affine equivalence
in the original ambient cube. -/
theorem presented_equivalence {s k : ℕ}
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^2 < 8*k)
    {B : Finset (𝔽₂ (2*(s+1)))} (ref : ShortestOddCircuit B B) (size : B.card=2*s+3)
    (full : Submodule.span F (B : Set (𝔽₂ (2*(s+1))))=⊤)
    {row target : 𝔽₂ (2*(s+1)) → Finset Four}
    (r : ∀ i∈B,(row i).Nonempty) (t : ∀ i∈B,(target i).Nonempty)
    (sr : (layers B row).card=k) (st : (layers B target).card=k)
    {S T : Finset (𝔽₂ (2*(s+1)+2))} (a : Presents B row S) (b : Presents B target T) :
    AffineRelated S T ↔ ∃ (σ : Equiv.Perm ↥B) (u : Four ≃ₗ[F] Four), ∀ i : B,
      (row i.val).card=(target (σ i).val).card ∧
      ((row i.val).card=2 → u (∑ x∈row i.val,x)=∑ y∈target (σ i).val,y) := by
  classical
  obtain ⟨e,he⟩ := a
  obtain ⟨f,hf⟩ := b
  have left := AffineRelated.linear (layers B row) e
  have right := AffineRelated.linear (layers B target) f
  rw [he] at left
  rw [hf] at right
  have rows := four_fibre_equivalence ref ref full full row target r t
    (by rw [size,sr];exact margin near) (by rw [size,st];exact margin near)
  constructor
  · intro h
    exact rows.mp ((left.trans h.compl).trans right.symm)
  · intro h
    have h' : AffineRelated Sᶜ Tᶜ := (left.symm.trans (rows.mpr h)).trans right
    simpa only [compl_compl] using h'.compl

/-- A complete affine invariant for actual dense doubles, expressed by six frequencies:
three labelled size counts and the three direction counts up to permutation. -/
theorem dense_double_signatures {s k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^2 < 8*k) :
    ∃ B : Finset (𝔽₂ (2*(s+1))), ShortestOddCircuit B B ∧ B.card=2*s+3 ∧
      ∃ row : (countedDoubles (2*(s+1)+2) k (threshold (2*s))) → 𝔽₂ (2*(s+1)) → Finset Four,
      (∀ S, Presents B (row S) S.val) ∧
      (∀ S T, AffineRelated S.val T.val ↔
        (∀ j : Fin 3, frequency (fun i : B => kind (row S i.val)) (.inl j)=
          frequency (fun i : B => kind (row T i.val)) (.inl j)) ∧
        ∀ n : ℕ, frequency (fun d : Direction => frequency (fun i : B => kind (row S i.val)) (.inr d)) n =
          frequency (fun d : Direction => frequency (fun i : B => kind (row T i.val)) (.inr d)) n) := by
  classical
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  choose row live sz presents using fun (S : countedDoubles (2*(s+1)+2) k (threshold (2*s))) =>
    present_counted hs near ref size full S.property
  refine ⟨B,ref,size,row,presents,fun S T => ?_⟩
  exact (presented_equivalence near ref size full (live S) (live T) (sz S) (sz T) (presents S) (presents T)).trans
    (signature_iff (fun i : B => row S i.val) (fun i : B => row T i.val)
      (fun i => live S i.val i.property) (fun i => live T i.val i.property))

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.presented_equivalence

#print axioms Green51FrameIsomorphisms.dense_double_signatures
