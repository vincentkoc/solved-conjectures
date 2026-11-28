import Green51DenseDirectionRank
import Mathlib.Data.Finset.Preimage

/-! # Compressing an omission word to its within-row rank -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

theorem compress_direction_rank {I H K : Type*} [AddCommGroup H] [Module F H]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (f : H →ₗ[F] K) (inj : Function.Injective f) (w : I → Finset K)
    (rank : Module.finrank F (rowDirectionSpace w) ≤ Module.finrank F H) [FiniteDimensional F H] :
    ∃ a : I → Finset H, (∀ i,(a i).card=(w i).card) ∧
      WordMatch w (fun i => (a i).map ⟨f,inj⟩) := by
  classical
  let P := rowDirectionSpace w
  obtain ⟨g,hg⟩ := (finrank_le_iff_exists_linearMap (R := F) (M := P) (M' := H)).mp rank
  let e := LinearEquiv.ofInjective (f.comp g) (inj.comp hg)
  obtain ⟨u,hu⟩ := Submodule.exists_linearEquiv_restrict_eq e
  let shift (i : I) := (u.toEquiv.trans (Equiv.addRight (-u (rowOrigin (w i))))).toEmbedding
  let m (i : I) := (w i).map (shift i)
  let a (i : I) := (m i).preimage f inj.injOn
  have idrow (i : I) : (a i).map ⟨f,inj⟩ = m i := by
    change ((m i).preimage f inj.injOn).map _=m i
    rw [map_eq_image]
    change ((m i).preimage f inj.injOn).image f=m i
    rw [image_preimage]
    apply filter_eq_self.mpr
    intro x hx
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hx
    let v : P := ⟨z-rowOrigin (w i),Submodule.subset_span ⟨i,z,rowOrigin (w i),hz,rowOrigin_mem _ ⟨z,hz⟩,rfl⟩⟩
    refine ⟨g v,?_⟩
    change f (g v)=u z+ -u (rowOrigin (w i))
    rw [←sub_eq_add_neg,←map_sub]
    exact hu v
  refine ⟨a,fun i => ?_,Equiv.refl _,u,fun i => -u (rowOrigin (w i)),fun i => (idrow i).symm⟩
  simpa only [m,card_map] using congrArg card (idrow i)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.compress_direction_rank
