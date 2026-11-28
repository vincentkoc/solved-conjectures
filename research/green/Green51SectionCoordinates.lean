import Green51SimplexFibres
import Green51FlatSections

/-! # Affine coordinates for a fifteen-point section and its parallel fibres -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51SimplexSection
open Green51SimplexFibres
open scoped Classical Pointwise
namespace Green51SectionCoordinates
local notation "F" => ZMod 2
variable {n k : ℕ} {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Coordinates for a finite set contained in a single level of a nonconstant functional. -/
theorem chart (K : Cube (n+1) →ₗ[F] F) (non : K≠0) (a : Cube (n+1))
    (B : Finset (Cube (n+1))) (level : ∀x∈B,K x=K a) :
    ∃ (j : Cube n →ₗ[F] Cube (n+1)) (S : Finset (Cube n)), Function.Injective j ∧
      j.range=K.ker ∧ S.image (fun y => j y+a)=B := by
  classical
  have dim := Module.Dual.finrank_ker_add_one_of_ne_zero non
  have rank : Module.finrank F (Cube (n+1))=n+1 := by simp [Cube]
  let e : Cube n ≃ₗ[F] K.ker := LinearEquiv.ofFinrankEq _ _ (by
    rw [show Module.finrank F (Cube n)=n by simp [Cube]]; omega)
  let j := K.ker.subtype.comp e.toLinearMap
  let S := univ.filter fun y => j y+a∈B
  refine ⟨j,S,Subtype.val_injective.comp e.injective,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (e y).property
    · intro hx
      obtain ⟨y,hy⟩ := e.surjective ⟨x,hx⟩
      exact ⟨y,congrArg Subtype.val hy⟩
  · ext x
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hy).2
    · intro hx
      have hz : x-a∈K.ker := by change K (x-a)=0; rw [map_sub,level x hx,sub_self]
      obtain ⟨y,hy⟩ := e.surjective ⟨_,hz⟩
      have h : j y+a=x := by change (e y).val+a=x; rw [hy]; simp
      exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,h ▸ hx⟩,h⟩

theorem transfer (j : Cube k →ₗ[F] G) (inj : Function.Injective j) (t : G)
    {S : Finset (Cube k)} {A : Finset G} (inc : ∀x∈S,j x+t∈A)
    {p : Cube k} (flat : FlatAt S p) : FlatAt A (j p) := by
  obtain ⟨W,d,inside⟩ := flat
  refine ⟨W.map j,(W.equivMapOfInjective j inj).finrank_eq.symm.trans d,?_⟩
  rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
  obtain ⟨x,hx,y,hy,eq⟩ := mem_add.mp (inside ⟨w,hw,rfl⟩)
  change j p+j w∈A+A
  have h := add_mem_add (inc x hx) (inc y hy)
  change x+y=p+w at eq
  rw [←map_add,←eq,map_add]
  simpa only [add_add_add_comm (j x) t (j y) t,ZModModule.add_self,add_zero] using h

/-- A flat-free fifteen-label section is the standard simplex configuration in
coordinates with the same direction space as the original section. -/
theorem position (j : Cube 10 →ₗ[F] G) (inj : Function.Injective j) (a : G)
    (S : Finset (Cube 10)) (size : S.card=15) (avoid : ¬FlatAt S 0) :
    ∃ (L : Cube 10 →ₗ[F] G) (t : G), Function.Injective L ∧ L.range=j.range ∧
      core L t=S.image (fun x => j x+a) := by
  classical
  obtain ⟨g,b,eq⟩ := normal_form S size avoid
  let L := j.comp g.symm.toLinearMap
  refine ⟨L,a-L b,inj.comp g.symm.injective,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨_,rfl⟩
    · rintro ⟨y,rfl⟩
      exact ⟨g y,by simp [L]⟩
  · rw [core,←eq,image_image]
    apply image_congr
    intro x _
    simp only [Function.comp_apply,L,LinearMap.comp_apply,LinearEquiv.coe_coe,map_add,LinearEquiv.symm_apply_apply]
    abel

end Green51SectionCoordinates
#print axioms Green51SectionCoordinates.chart
#print axioms Green51SectionCoordinates.transfer
#print axioms Green51SectionCoordinates.position
