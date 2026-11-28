import Green51RowDifferenceKernels
import Green51SimplexPermutation

/-! # Affine equivalence from binary column relations -/

open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51SimplexSection
local notation "F" => ZMod 2
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

def augmented (a : Fin n → V) : Cube n →ₗ[F] F × V :=
  Fintype.linearCombination F (fun i => ((1:F),a i))

/-- Equal relations on the augmented columns recover the labelled configuration
up to a linear automorphism and one translation. -/
theorem affine_of_relations (o : Fin n) (a b : Fin n → V)
    (rel : (augmented a).ker=(augmented b).ker) :
    ∃ (g : V ≃ₗ[F] V) (t : V), ∀ i, g (a i)+t=b i := by
  let A i := a i - a o
  let B i := b i - b o
  have anchor (l : Fin n → V) (z : Cube n) :
      augmented l (z-Pi.single o (∑ i,z i)) =
        (0, Fintype.linearCombination F (fun i => l i - l o) z) := by
    rw [map_sub]
    change Fintype.linearCombination F (fun i => ((1:F),l i)) z -
      Fintype.linearCombination F (fun i => ((1:F),l i)) (Pi.single o (∑ i,z i)) = _
    rw [Fintype.linearCombination_apply_single]
    apply Prod.ext
    · simp [Fintype.linearCombination_apply, Prod.fst_sum]
    · simp [Fintype.linearCombination_apply, Prod.snd_sum, smul_sub, sum_sub_distrib, sum_smul]
  have ker : LinearMap.ker (Finsupp.linearCombination F A)=
      LinearMap.ker (Finsupp.linearCombination F B) := by
    ext c
    obtain ⟨z,rfl⟩ := (Finsupp.linearEquivFunOnFinite F F (Fin n)).symm.surjective c
    change Finsupp.linearCombination F A _ = 0 ↔ Finsupp.linearCombination F B _ = 0
    rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply,
        Finsupp.linearCombination_eq_fintype_linearCombination_apply]
    have h := SetLike.ext_iff.mp rel (z-Pi.single o (∑ i,z i))
    change augmented a _=0 ↔ augmented b _=0 at h
    simpa [anchor, A, B, Prod.ext_iff] using h
  obtain ⟨g,hg⟩ := (Green51FrameIsomorphisms.tuple_ker_iff A B).mp ker
  refine ⟨g,b o-g (a o),fun i => ?_⟩
  have h := hg i
  change g (a i-a o)=b i-b o at h
  rw [map_sub] at h
  abel_nf at h ⊢
  linear_combination (norm := abel) h

/-- Reindexing the input of an augmented sum permutes its labelled columns. -/
theorem augmented_reindex (a : Fin n → V) (σ : Equiv.Perm (Fin n)) (z : Cube n) :
    augmented (fun i => a (σ.symm i)) z = augmented a (fun i => z (σ i)) := by
  change (∑ i, z i • ((1:F), a (σ.symm i))) = ∑ i, z (σ i) • ((1:F),a i)
  simpa using σ.symm.sum_comp (fun i => z (σ i) • ((1:F),a i))

end Green51SimplexSection
#print axioms Green51SimplexSection.affine_of_relations
#print axioms Green51SimplexSection.augmented_reindex
