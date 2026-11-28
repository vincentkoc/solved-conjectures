import Green51TranslationClasses
import Green51FrameAutocorrelation

/-! # Recognition of a circuit fibre space under changes of affine coordinates -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51OriginRecovery
open scoped Classical Pointwise
variable {G H : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [DecidableEq H]

theorem lag_linear (u : G ≃ₗ[F] H) (D : Finset G) (t : G) :
    lag (D.map u.toEquiv.toEmbedding) (u t)=lag D t := by
  classical
  unfold lag
  apply card_bij (fun x _ => u.symm x)
  · intro x hx
    obtain ⟨orig,moved⟩ := mem_filter.mp hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp orig
    obtain ⟨z,hz,eq⟩ := mem_map.mp moved
    change u z=u y+u t at eq
    rw [←map_add] at eq
    apply mem_filter.mpr
    change u.symm (u y)∈D ∧ u.symm (u y)+t∈D
    simpa only [LinearEquiv.symm_apply_apply] using And.intro hy ((u.injective eq) ▸ hz)
  · intro x _ y _ eq;exact u.symm.injective eq
  · intro y hy
    obtain ⟨old,moved⟩ := mem_filter.mp hy
    refine ⟨u y,mem_filter.mpr ⟨mem_map_of_mem _ old,?_⟩,u.symm_apply_apply y⟩
    rw [←map_add];exact mem_map_of_mem _ moved

variable [Fintype G] [Fintype H]

theorem affine_recovers_space {C E D : Finset G} {B L M : Finset H}
    (m : ShortestOddCircuit E C) (n : ShortestOddCircuit L B)
    (P : Submodule F G) (Q : Submodule F H)
    (comp : IsCompl P (Submodule.span F (C : Set G)))
    (other : IsCompl Q (Submodule.span F (B : Set H)))
    (sub : D ⊆ (P : Set G).toFinset+C) (sub' : M ⊆ (Q : Set H).toFinset+B)
    (large : ((P : Set G).toFinset+C).card+2*(P : Set G).toFinset.card < 2*D.card)
    (large' : ((Q : Set H).toFinset+B).card+2*(Q : Set H).toFinset.card < 2*M.card)
    (size : (P : Set G).toFinset.card=(Q : Set H).toFinset.card)
    (u : G ≃ₗ[F] H) (b : H) (eq : M=Green51OriginRecovery.translate (D.map u.toEquiv.toEmbedding) b) :
    ∀ t, t∈P ↔ u t∈Q := by
  intro t
  rw [recover_period m P comp sub large,recover_period n Q other sub' large',size,eq]
  exact Iff.of_eq (congrArg (2*(Q : Set H).toFinset.card < ·)
    ((lag_shift (D.map u.toEquiv.toEmbedding) b (u t)).trans (lag_linear u D t)).symm)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.lag_linear
#print axioms Green51FrameIsomorphisms.affine_recovers_space
