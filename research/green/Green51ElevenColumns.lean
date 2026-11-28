import Green51ElevenRelations

/-! # Affine hyperplanes and the augmented columns of a binary set -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51ElevenColumns
local notation "F" => ZMod 2
abbrev V := Cube 11

theorem flat_mono {B A : Finset V} (sub : B⊆A) {p : V} (h : FlatAt B p) :
    FlatAt A p := by
  obtain ⟨W,d,hw⟩ := h
  exact ⟨W,d,fun _ hx => add_subset_add sub sub (hw hx)⟩

/-- Sixteen labels in a ten-dimensional affine hyperplane already force
an affine three-space in their double. -/
theorem affine_of_hyperplane (A : Finset V) (large : 16≤A.card) (L : V →ₗ[F] F)
    (non : L≠0) (a : V) (level : ∀x∈A,L x=L a) : ∃p, FlatAt A p := by
  classical
  obtain ⟨B,sub,size⟩ := exists_subset_card_eq large
  have dim := Module.Dual.finrank_ker_add_one_of_ne_zero non
  have rank : Module.finrank F V=11 := by simp [V,Cube]
  let j : Cube 10 ≃ₗ[F] L.ker := LinearEquiv.ofFinrankEq _ _ (by
    rw [show Module.finrank F (Cube 10)=10 by simp [Cube]]; omega)
  let f := L.ker.subtype.comp j.toLinearMap
  have inj : Function.Injective f := Subtype.val_injective.comp j.injective
  let S := univ.filter fun y => a+f y∈B
  have covers : S.image (fun y => a+f y)=B := by
    ext x
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hy).2
    · intro hx
      have hz : x-a∈L.ker := by change L (x-a)=0; rw [map_sub,level x (sub hx),sub_self]
      obtain ⟨y,hy⟩ := j.surjective ⟨_,hz⟩
      have h : a+f y=x := by change a+(j y).val=x; rw [hy]; simp
      exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,h ▸ hx⟩,h⟩
  have eqsize : S.card=16 := by
    rw [←size,←covers,card_image_of_injective]
    exact fun y z e => inj (add_left_cancel e)
  obtain ⟨W,c,d,inside⟩ := Green51FirstSeparation.sixteen_affine S eqsize
  refine ⟨f c,flat_mono sub ⟨W.map f,(W.equivMapOfInjective f inj).finrank_eq.symm.trans d,?_⟩⟩
  rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
  obtain ⟨s,hs,t,ht,eq⟩ := mem_add.mp (inside w hw)
  have h := add_mem_add ((mem_filter.mp hs).2) ((mem_filter.mp ht).2)
  change f c+f w∈B+B
  have same := congrArg f eq
  rw [map_add,map_add] at same
  rw [←same]
  simpa only [add_add_add_comm a _ a _,ZModModule.add_self,zero_add] using h

/-- Any sixteen surviving columns of an affine-flat-free configuration
span the full twelve-dimensional augmented space. -/
theorem columns_span (B : Finset V) (large : 16≤B.card) (avoid : ¬∃p,FlatAt B p) :
    Submodule.span F ((fun x:V => ((1:F),x)) '' (B:Set V))=⊤ := by
  classical
  let S := Submodule.span F ((fun x:V => ((1:F),x)) '' (B:Set V))
  by_contra h
  obtain ⟨l,non,vanish⟩ := S.exists_dual_map_eq_bot_of_lt_top
    (show S<⊤ from lt_top_iff_ne_top.mpr h) inferInstance
  have zero (x:V) (hx:x∈B) : l (1,x)=0 := by
    have inS : ((1:F),x)∈S := Submodule.subset_span ⟨x,hx,rfl⟩
    have mem : l (1,x)∈S.map l := Submodule.mem_map.mpr ⟨_,inS,rfl⟩
    simpa only [vanish,Submodule.mem_bot] using mem
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<B.card by omega)
  let L : V →ₗ[F] F := l.comp (LinearMap.inr F F V)
  have split (x:V) : l (1,x)=l (1,0)+L x :=
    by simpa only [Prod.mk_add_mk,add_zero,zero_add,L,LinearMap.comp_apply,LinearMap.inr_apply] using
         map_add l ((1:F),(0:V)) (0,x)
  have nz : L≠0 := by
    intro off
    have base := zero a ha
    rw [split,off,LinearMap.zero_apply,add_zero] at base
    apply non
    apply LinearMap.ext
    rintro ⟨c,x⟩
    rcases (show ∀b:F,b=0 ∨ b=1 from by decide) c with rfl|rfl
    · exact LinearMap.congr_fun off x
    · change l (1,x)=0
      rw [split,off,LinearMap.zero_apply,base,add_zero]
  apply avoid (affine_of_hyperplane B large L nz a ?_)
  intro x hx
  exact add_left_cancel ((split x).symm.trans ((zero x hx).trans ((zero a ha).symm.trans (split a))))

end Green51ElevenColumns
#print axioms Green51ElevenColumns.affine_of_hyperplane
#print axioms Green51ElevenColumns.columns_span
