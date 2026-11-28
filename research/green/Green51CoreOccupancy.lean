import Green51SectionCoordinates
import Green51FirstSeparation

/-! # The affine ten-space spanned by a simplex section contains no extra label -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51SimplexSection
open Green51SimplexFibres Green51SectionCoordinates
open scoped Classical Pointwise
namespace Green51CoreOccupancy
local notation "F" => ZMod 2
variable {G:Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

theorem exact_fibre {A:Finset G} (L:Cube 10 →ₗ[F] G) (inj:Function.Injective L)
    (t:G) (inc:core L t⊆A) (avoid:¬∃p,FlatAt A p) {x:G} (hx:x∈A) :
    L.range.mkQ x=L.range.mkQ t ↔ x∈core L t := by
  classical
  constructor
  · intro same
    have hz : x-t∈L.range := (Submodule.Quotient.mk_eq_zero L.range).mp (by
      change L.range.mkQ (x-t)=0;rw [map_sub,same,sub_self])
    obtain ⟨v,hv⟩ := hz
    have ix : L v+t=x := by rw [hv,sub_add_cancel]
    by_contra miss
    have away : v∉model := fun h => miss (ix ▸ mem_image_of_mem _ h)
    have full := Green51FirstSeparation.sixteen_affine (insert v model)
      (by rw [card_insert_of_notMem away,model_card])
    obtain ⟨W,p,d,inside⟩ := full
    have flat : FlatAt (insert v model) p := by
      refine ⟨W,d,?_⟩
      rintro _ ⟨w,hw,rfl⟩;exact inside w hw
    apply avoid ⟨_,transfer L inj t (A:=A) (S:=insert v model) ?_ flat⟩
    intro y hy
    rcases mem_insert.mp hy with rfl|h
    · exact ix.symm ▸ hx
    · exact inc (mem_image_of_mem _ h)
  · intro hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    rw [map_add,show L.range.mkQ (L v)=0 from
      (Submodule.Quotient.mk_eq_zero L.range).mpr ⟨v,rfl⟩,zero_add]

end Green51CoreOccupancy
#print axioms Green51CoreOccupancy.exact_fibre
