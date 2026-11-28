import Green51TenDimensions

/-! # Transporting binary sumset thresholds through affine hyperplanes -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51FlatSections
local notation "F" => ZMod 2
variable {n k : ℕ}

theorem flat_mono {B A : Finset (Cube (n+1))} (sub : B⊆A) {p : Cube (n+1)} (h : FlatAt B p) :
    FlatAt A p := by
  obtain ⟨W,d,hw⟩ := h
  exact ⟨W,d,fun _ hx => add_subset_add sub sub (hw hx)⟩

/-- A cardinal threshold in a binary space applies on each affine hyperplane one dimension higher. -/
theorem affine_of_hyperplane (cutoff : ∀ S : Finset (Cube n), S.card=k → ∃ p, FlatAt S p)
    (A : Finset (Cube (n+1))) (large : k≤A.card) (L : Cube (n+1) →ₗ[F] F)
    (non : L≠0) (a : Cube (n+1)) (level : ∀x∈A,L x=L a) : ∃p, FlatAt A p := by
  classical
  obtain ⟨B,sub,size⟩ := exists_subset_card_eq large
  have dim := Module.Dual.finrank_ker_add_one_of_ne_zero non
  have rank : Module.finrank F (Cube (n+1))=n+1 := by simp [Cube]
  let j : Cube n ≃ₗ[F] L.ker := LinearEquiv.ofFinrankEq _ _ (by
    rw [show Module.finrank F (Cube n)=n by simp [Cube]]; omega)
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
  have eqsize : S.card=k := by
    rw [←size,←covers,card_image_of_injective]
    exact fun y z e => inj (add_left_cancel e)
  obtain ⟨c,W,d,inside⟩ := cutoff S eqsize
  refine ⟨f c,flat_mono sub ⟨W.map f,(W.equivMapOfInjective f inj).finrank_eq.symm.trans d,?_⟩⟩
  rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
  obtain ⟨s,hs,t,ht,eq⟩ := mem_add.mp (inside ⟨w,hw,rfl⟩)
  have h := add_mem_add ((mem_filter.mp hs).2) ((mem_filter.mp ht).2)
  change f c+f w∈B+B
  change s+t=c+w at eq
  have same := congrArg f eq
  rw [map_add,map_add] at same
  rw [←same]
  simpa only [add_add_add_comm a _ a _,ZModModule.add_self,zero_add] using h

/-- Every flat-free set above the hyperplane cutoff has full augmented column span. -/
theorem columns_span (cutoff : ∀ S : Finset (Cube n), S.card=k → ∃ p, FlatAt S p)
    (pos : 0<k) (B : Finset (Cube (n+1))) (large : k≤B.card) (avoid : ¬∃p,FlatAt B p) :
    Submodule.span F ((fun x:Cube (n+1) => ((1:F),x)) '' (B:Set (Cube (n+1))))=⊤ := by
  classical
  let S := Submodule.span F ((fun x:Cube (n+1) => ((1:F),x)) '' (B:Set (Cube (n+1))))
  by_contra h
  obtain ⟨l,non,vanish⟩ := S.exists_dual_map_eq_bot_of_lt_top
    (show S<⊤ from lt_top_iff_ne_top.mpr h) inferInstance
  have zero (x:Cube (n+1)) (hx:x∈B) : l (1,x)=0 := by
    have inS : ((1:F),x)∈S := Submodule.subset_span ⟨x,hx,rfl⟩
    have mem : l (1,x)∈S.map l := Submodule.mem_map.mpr ⟨_,inS,rfl⟩
    simpa only [vanish,Submodule.mem_bot] using mem
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<B.card by omega)
  let L : Cube (n+1) →ₗ[F] F := l.comp (LinearMap.inr F F (Cube (n+1)))
  have split (x:Cube (n+1)) : l (1,x)=l (1,0)+L x :=
    by simpa only [Prod.mk_add_mk,add_zero,zero_add,L,LinearMap.comp_apply,LinearMap.inr_apply] using
         map_add l ((1:F),(0:Cube (n+1))) (0,x)
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
  apply avoid (affine_of_hyperplane cutoff B large L nz a ?_)
  intro x hx
  exact add_left_cancel ((split x).symm.trans ((zero x hx).trans ((zero a ha).symm.trans (split a))))

end Green51FlatSections
#print axioms Green51FlatSections.flat_mono
#print axioms Green51FlatSections.affine_of_hyperplane
#print axioms Green51FlatSections.columns_span
