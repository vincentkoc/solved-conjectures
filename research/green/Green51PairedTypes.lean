import Green51PairedRelations
import Green51TenDimensions

/-! # Affine classification of sixteen-label three-space witnesses -/

open Finset Green50Downsets Green50Sharp Green51LocalFlats
open scoped Classical Pointwise
namespace Green51PairedTypes
local notation "F" => ZMod 2
abbrev Even := parity.ker
def origin : Space := label (0,0)
def point (i : Slots) : Even :=
  ⟨label i+origin,by simp [origin,LinearMap.mem_ker,map_add,parity_label,ZModModule.add_self]⟩
def largeModel : Finset Even := univ.image point
def diagonal : Even := ⟨(fun _=>1,0),by change (∑ _z:Positions,(1:F))=0; decide +kernel⟩
def line : Submodule F Even := F ∙ diagonal
noncomputable def smallModel : Finset (Even ⧸ line) := largeModel.image line.mkQ

theorem rank_large : Module.finrank F Even=11 := by
  have h : parity≠0 := fun e => by
    have h := parity_label (0,0)
    rw [e,LinearMap.zero_apply] at h
    exact zero_ne_one h
  have d := Module.Dual.finrank_ker_add_one_of_ne_zero h
  have sz : Module.finrank F Space=12 := by simp [Space,Ambient,Alphabet,Cube,Module.finrank_prod]
  change Module.finrank F Even+1=_ at d
  omega

theorem rank_small : Module.finrank F (Even ⧸ line)=10 := by
  have neq : diagonal≠0 := by
    intro h
    exact one_ne_zero (congrArg (fun x:Even => x.val.1 0) h)
  have rank := line.finrank_quotient_add_finrank
  rw [show Module.finrank F line=1 from finrank_span_singleton neq,rank_large] at rank
  omega

private def gain (r : Positions→F) : (Positions→F) →ₗ[F] (F×Positions) :=
  Fintype.linearCombination F (fun z => (r z,r z • z))
private def shear (r : Positions→F) : Space →ₗ[F] Space :=
  let fst := LinearMap.fst F (Positions→F) (F×Positions)
  fst.prod (LinearMap.snd F _ _ + (gain r).comp fst)
private def swap (r : Positions→F) (i : Slots) : Slots := (i.1,i.2+r i.1)
private theorem swap_twice (r : Positions→F) (i : Slots) : swap r (swap r i)=i := by
  rcases i with ⟨z,b⟩; simp [swap,add_assoc,ZModModule.add_self]
private theorem shear_label (r : Positions→F) (i : Slots) :
    shear r (label i)=label (swap r i) := by
  rcases i with ⟨z,b⟩
  have at_single : gain r (Pi.single z 1)=(r z,r z • z) := by
    simp [gain,Fintype.linearCombination_apply,Pi.single_apply,ite_smul]
  simp [shear,label,swap,at_single,add_smul]
private theorem shear_diagonal (v : F×Positions) :
    ∃ r : Positions→F,shear r diagonal.val=(fun _=>1,v) := by
  exact (show ∀ v : F×Positions,∃ r : Positions→F,shear r diagonal.val=(fun _=>1,v)
    from by decide +kernel) v

open Green51TenDimensions
variable {E G : Type*} [AddCommGroup E] [Module F E]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A translated injective linear image of a finite configuration. -/
def AffineCopy (B : Finset E) (A : Finset G) : Prop :=
  ∃ (f : E →ₗ[F] G) (t : G), Function.Injective f ∧ B.image (fun x => t+f x)=A

/-- A minimum-size set whose double separates affine and linear three-spaces. -/
def Witness (A : Finset G) : Prop :=
  A.card=16 ∧ (¬FlatAt A 0) ∧ ∃ p,FlatAt A p

private theorem represented_flat {d:ℕ} (W : Submodule F G) (p : G)
    (f : Ambient d →ₗ[F] G) (j : Cube d ≃ₗ[F] W)
    (lifts : ∀ z : Cube d,f (0,1,z)=p+(j z).val) :
    p +ᵥ (W:Set G) ⊆ ↑((labels d).image f+(labels d).image f) := by
  have represented (z:Cube d) :
      f (0,1,z)∈(labels d).image f+(labels d).image f := by
    have eq : leftPoint z+rightPoint z=(0,1,z) := by
      simp [leftPoint,rightPoint,Prod.mk_add_mk,ZModModule.add_self]
    have hl : leftPoint z ∈ labels d := mem_union_left _ (mem_image_of_mem leftPoint (mem_univ z))
    have hr : rightPoint z ∈ labels d := mem_union_right _ (mem_image_of_mem rightPoint (mem_univ z))
    rw [←eq,map_add]
    exact add_mem_add (mem_image_of_mem f hl) (mem_image_of_mem f hr)
  apply Set.image_subset_iff.mpr
  intro w hw
  obtain ⟨z,hz⟩ := j.surjective ⟨w,hw⟩
  simp only [Set.mem_preimage,mem_coe,vadd_eq_add]
  simpa only [lifts,hz] using represented z

private theorem avoids_subset (A B : Finset G) (sub : B⊆A) (avoid : ¬FlatAt A 0) :
    ¬∃ V : Submodule F G,Module.finrank F V=3 ∧ ∀ v∈V,v∈B+B := by
  rintro ⟨V,n,inside⟩
  exact avoid ((flat_zero A).mpr ⟨V,n,fun v hv => add_subset_add sub sub (inside v hv)⟩)

private theorem presentation [Fintype G] {A : Finset G} (h : Witness A) :
    ∃ f : Space →ₗ[F] G, univ.image (fun i => f (label i))=A ∧
      Function.Injective (fun i => f (label i)) := by
  obtain ⟨size,avoid,p,W,rank,flat⟩ := h
  obtain ⟨f,j,sub,lifts⟩ := model_image A W rank p flat
  let B := (labels 3).image f
  have retains := represented_flat W p f j lifts
  have avoidB := avoids_subset A B sub avoid
  have cost := Green51AffineMatchings.affine_flat_cost B avoidB W p retains rank.ge
  rw [rank] at cost
  have equal : B=A := eq_of_subset_of_card_le sub (by rw [size];exact cost)
  have image : univ.image (fun i => f (label i))=A := by
    simpa only [B,labels_eq,image_image,Function.comp_def] using equal
  refine ⟨f,image,?_⟩
  have eqcard : (univ.image (fun i => f (label i))).card=(univ : Finset Slots).card := by
    rw [image,size];decide +kernel
  exact fun _ _ eq => (card_image_iff.mp eqcard) (mem_univ _) (mem_univ _) eq

private theorem anchored (f : Space →ₗ[F] G) :
    largeModel.image (fun x => f origin+f x.val)=univ.image (fun i => f (label i)) := by
  simp only [largeModel,image_image]
  apply image_congr
  intro i _
  change f origin+f (label i+origin)=f (label i)
  rw [map_add,add_left_comm,ZModModule.add_self,add_zero]

private theorem permuted (f : Space →ₗ[F] G) (r : Positions→F) :
    univ.image (fun i => f (shear r (label i)))=univ.image (fun i => f (label i)) := by
  simp only [shear_label]
  ext y
  constructor
  · intro h;obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact mem_image_of_mem (fun i => f (label i)) (mem_univ (swap r i))
  · intro h;obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact mem_image.mpr ⟨swap r i,mem_univ _,by rw [swap_twice]⟩

/-- Every minimum witness is an affine copy of one of the two models. -/
theorem of_witness [Fintype G] {A : Finset G} (h : Witness A) :
    AffineCopy largeModel A ∨ AffineCopy smallModel A := by
  obtain ⟨f,image,inj⟩ := presentation h
  have size := h.1
  have avoid := fun ex => h.2.1 ((flat_zero A).mpr ex)
  by_cases trivial : ∀ x:Even,f x.val=0 → x=0
  · left
    let g := f.comp parity.ker.subtype
    have injective : Function.Injective g := LinearMap.ker_eq_bot.mp
      (eq_bot_iff.mpr (fun x hx => (Submodule.mem_bot F).mpr (trivial x hx)))
    exact ⟨g,f origin,injective,(anchored f).trans image⟩
  · push Not at trivial
    obtain ⟨x,kx,nx⟩ := trivial
    have inside (i:Slots) : f (label i)∈A := image ▸ mem_image_of_mem _ (mem_univ i)
    have nonzero : x.val≠0 := fun e => nx (Subtype.ext e)
    have all := full_horizontal A (by omega) avoid f inside inj nonzero kx x.property
    obtain ⟨r,hr⟩ := shear_diagonal x.val.2
    let g := f.comp (shear r)
    have gd : g diagonal.val=0 := by
      change f (shear r diagonal.val)=0
      rw [hr,←all];exact kx
    have im : univ.image (fun i => g (label i))=A := (permuted f r).trans image
    have gi : Function.Injective (fun i => g (label i)) := by
      intro a b eq
      change f (shear r (label a))=f (shear r (label b)) at eq
      simp only [shear_label] at eq
      exact (show Function.Involutive (swap r) from swap_twice r).injective (inj eq)
    have horizontal_kernel {y : Even} (nz : y≠0) (zero : g y.val=0) :
        y.val.1=(fun _=>1) := by
      exact full_horizontal A (by omega) avoid g (fun i => im ▸ mem_image_of_mem _ (mem_univ i))
        gi (fun e => nz (Subtype.ext e)) zero y.property
    let k := g.comp parity.ker.subtype
    have kernel : line=k.ker := by
      apply le_antisymm
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr gd)
      · intro y hy
        by_cases yz : y=0
        · rw [yz];exact line.zero_mem
        have top := horizontal_kernel yz hy
        have sum : y+diagonal=0 := by
          by_contra ne
          have zero : g (y+diagonal).val=0 := by
            change g (y.val+diagonal.val)=0
            rw [map_add,show g y.val=0 from hy,gd,add_zero]
          have bad := congrFun (horizontal_kernel ne zero) 0
          change y.val.1 0+1=1 at bad
          rw [top] at bad
          exact (by decide : ¬((1:F)+1=1)) bad
        have eq : y=diagonal := add_right_cancel (sum.trans (ZModModule.add_self _).symm)
        exact eq ▸ Submodule.subset_span (Set.mem_singleton _)
    right
    refine ⟨line.liftQ k kernel.le,g origin,LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot' line k kernel),?_⟩
    rw [smallModel,image_image]
    exact (anchored g).trans im

/-- Linear span of the pair sums, the direction space of a nonempty binary configuration. -/
def directions (A : Finset G) : Submodule F G := Submodule.span F (↑(A+A):Set G)

theorem translated_double (A : Finset G) (t : G) :
    A.image (fun x => t+x)+A.image (fun x => t+x)=A+A := by
  ext y
  constructor
  · intro hy
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp hy
    obtain ⟨a',ha',rfl⟩ := mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := mem_image.mp hb
    rw [add_add_add_comm,ZModModule.add_self,zero_add] at eq
    exact mem_add.mpr ⟨a',ha',b',hb',eq⟩
  · intro hy
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp hy
    exact mem_add.mpr ⟨t+a,mem_image_of_mem _ ha,t+b,mem_image_of_mem _ hb,by
      rwa [add_add_add_comm,ZModModule.add_self,zero_add]⟩

private theorem directions_image [DecidableEq E] (f : E →ₗ[F] G) (B : Finset E) :
    directions (B.image f)=(directions B).map f := by
  rw [directions,directions,←image_add,Submodule.map_span,coe_image]

theorem directions_large : directions largeModel=⊤ := by
  let S := directions largeModel
  have zero : (0:Even)∈largeModel := by
    have eq : point (0,0)=0 := Subtype.ext (ZModModule.add_self _)
    exact eq ▸ mem_image_of_mem point (mem_univ (0,0))
  have bound := Green51LocalFlats.label_rank (S.map parity.ker.subtype) origin (by
    intro v hv
    rw [labels_eq] at hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    refine ⟨point i,Submodule.subset_span ?_,rfl⟩
    exact mem_add.mpr ⟨point i,mem_image_of_mem point (mem_univ i),0,zero,add_zero _⟩)
  have dim := (S.equivMapOfInjective parity.ker.subtype Subtype.val_injective).finrank_eq
  have low : 11≤Module.finrank F S := bound.trans_eq dim.symm
  have upper := Submodule.finrank_le S
  rw [rank_large] at upper
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank F S=_
  rw [rank_large]
  exact Nat.le_antisymm upper low

theorem directions_small : directions smallModel=⊤ := by
  rw [smallModel,directions_image,directions_large,Submodule.map_top,Submodule.range_mkQ]

theorem copy_rank [DecidableEq E] [Module.Finite F E] {B : Finset E} {A : Finset G}
    (h : AffineCopy B A) : Module.finrank F (directions A)=Module.finrank F (directions B) := by
  obtain ⟨f,t,inj,rfl⟩ := h
  have img : B.image (fun x => t+f x)=(B.image f).image (fun x => t+x) := by simp only [image_image,Function.comp_def]
  rw [img]
  have eq : directions ((B.image f).image (fun x => t+x))=directions (B.image f) := by
    rw [directions,directions,translated_double]
  rw [eq,directions_image]
  exact ((directions B).equivMapOfInjective f inj).finrank_eq.symm

theorem witness_copy [DecidableEq E] {B : Finset E} {A : Finset G} (h : AffineCopy B A) :
    Witness A ↔ Witness B := by
  obtain ⟨f,t,inj,rfl⟩ := h
  have trans : Function.Injective (fun x:G => t+x) := fun _ _ eq => add_left_cancel eq
  have img : B.image (fun x => t+f x)=(B.image f).image (fun x => t+x) := by simp only [image_image,Function.comp_def]
  have same (p:G) : FlatAt ((B.image f).image (fun x => t+x)) p ↔ FlatAt (B.image f) p := by
    simp only [FlatAt,translated_double]
  rw [img,Witness,Witness,card_image_of_injective _ trans,card_image_of_injective _ inj]
  simp only [same]
  exact and_congr_right fun _ => separates_image f inj B

theorem large_witness : Witness largeModel := by
  have copy : AffineCopy largeModel (labels 3) := by
    refine ⟨parity.ker.subtype,origin,Subtype.val_injective,?_⟩
    simpa only [labels_eq,LinearMap.id_apply,Submodule.subtype_apply] using anchored (LinearMap.id (R:=F) (M:=Space))
  apply (witness_copy copy).mp
  obtain ⟨W,p,rank,inside⟩ := model_flat 3
  refine ⟨label_count 3,?_,p,W,rank,inside⟩
  intro h
  obtain ⟨V,sz,sub⟩ := (flat_zero _).mp h
  have bound := Green51SparseDimensions.rank_without_relation (labels 3) (label_free 3) V sub
  omega

theorem small_witness : Witness smallModel := by
  obtain ⟨A,sz,avoid,W,p,rank,inside⟩ := sixteen_in_ten
  have h : Witness A := ⟨sz,fun ex => avoid ((flat_zero A).mp ex),p,W,rank,inside⟩
  rcases of_witness h with big|small
  · obtain ⟨f,_,inj,_⟩ := big
    have too := LinearMap.finrank_le_finrank_of_injective inj
    rw [rank_large] at too
    simp [Cube] at too
  · exact (witness_copy small).mp h

/-- The complete affine classification in arbitrary finite binary spaces. -/
theorem witness_iff [Fintype G] (A : Finset G) :
    Witness A ↔ AffineCopy largeModel A ∨ AffineCopy smallModel A := by
  refine ⟨of_witness,?_⟩
  rintro (big|small)
  · exact (witness_copy big).mpr large_witness
  · exact (witness_copy small).mpr small_witness

/-- The affine dimension distinguishes the two types in every ambient space. -/
theorem distinct_types (A : Finset G) :
    ¬(AffineCopy largeModel A ∧ AffineCopy smallModel A) := by
  rintro ⟨big,small⟩
  have h := (copy_rank big).symm.trans (copy_rank small)
  rw [directions_large,directions_small,finrank_top,finrank_top,rank_large,rank_small] at h
  contradiction

end Green51PairedTypes

#print axioms Green51PairedTypes.rank_large
#print axioms Green51PairedTypes.rank_small
#print axioms Green51PairedTypes.of_witness
#print axioms Green51PairedTypes.translated_double
#print axioms Green51PairedTypes.directions_large
#print axioms Green51PairedTypes.directions_small
#print axioms Green51PairedTypes.copy_rank
#print axioms Green51PairedTypes.witness_copy
#print axioms Green51PairedTypes.large_witness
#print axioms Green51PairedTypes.small_witness
#print axioms Green51PairedTypes.witness_iff
#print axioms Green51PairedTypes.distinct_types
