import Green51QuadraticFlats
import Green51PairedTypes

/-! # Counting the three-spaces in sixteen-label witnesses -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise
namespace Green51WitnessIncidence
local notation "F" => ZMod 2

private theorem affine_bit_count {d:ℕ} (a:F) (l:Cube d →ₗ[F] F) {w:Cube d}
    (one : a+l w=1) :
    2^d≤2*(univ.filter (fun z => a+l z=1)).card := by
  let S := univ.filter (fun z => a+l z=1)
  by_cases all : ∀ z,a+l z=1
  · have eq : S=univ := filter_true_of_mem (fun i _ => all i)
    change _≤2*S.card
    rw [eq,card_univ]
    simp [Cube]
  · push Not at all
    obtain ⟨u,hu⟩ := all
    have bit : a+l u=0 := ((show ∀ b:F,b=0 ∨ b=1 from by decide) _).resolve_right hu
    let t := w+u
    have flip : l t=1 := by
      have h := congrArg₂ (·+·) one bit
      rw [add_add_add_comm,ZModModule.add_self,zero_add,add_zero] at h
      exact (l.map_add _ _).trans h
    have cover : univ⊆S∪S.image (fun z => z+t) := by
      intro z _
      by_cases hit:a+l z=1
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hit⟩)
      · have zero : a+l z=0 := ((show ∀ b:F,b=0 ∨ b=1 from by decide) _).resolve_right hit
        exact mem_union_right _ (mem_image.mpr ⟨z+t,mem_filter.mpr ⟨mem_univ _,by
          rw [map_add,←add_assoc,zero,flip,zero_add]⟩,by rw [add_assoc,ZModModule.add_self,add_zero]⟩)
    have bound := (card_le_card cover).trans (card_union_le _ _)
    rw [card_univ,card_image_of_injective _ (fun _ _ e => add_right_cancel e)] at bound
    simpa only [S,Cube,Fintype.card_fun,Fintype.card_fin,ZMod.card,two_mul] using bound

variable {G:Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]

/-- A flat meeting the one level of a linear functional needs at least
half its cardinality in each input level. -/
theorem hyperplane_cost {d:ℕ} (large:3≤d) (A:Finset G)
    (avoid:¬∃ W:Submodule F G,Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A)
    (W:Submodule F G) (dim:Module.finrank F W=d) (p:G) (inside:p +ᵥ (W:Set G)⊆↑(A+A))
    (f:G →ₗ[F] F) {y:G} (hy:y∈p +ᵥ (W:Set G)) (high:f y=1) (b:F) :
    2^d≤2*(A.filter (fun x => f x=b)).card := by
  let j : Cube d ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by simp [Cube,dim])
  let L := W.subtype.comp j.toLinearMap
  have pairs (z:Cube d) : ∃ x∈A,∃ y∈A,x+y=p+L z := mem_add.mp (inside ⟨_,(j z).property,rfl⟩)
  choose x hx v hv eq using pairs
  let a (i:Cube d×F) := if i.2=0 then x i.1 else v i.1
  have a0 (z:Cube d) : a (z,0)=x z := by simp [a]
  have a1 (z:Cube d) : a (z,1)=v z := by simp [a]
  have inA (i) : a i∈A := by dsimp [a];split <;> first | apply hx | apply hv
  have sums (z) : a (z,0)+a (z,1)=p+L z := by rw [a0,a1,eq]
  have uniq := disjoint_representatives large A avoid a inA p L
    (Subtype.val_injective.comp j.injective) sums
  obtain ⟨w,hw,ey⟩ := (show ∃ w∈W,p+w=y from hy)
  obtain ⟨z,hz⟩ := j.surjective ⟨w,hw⟩
  have fat : f p+f (L z)=1 := by simpa only [L,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Submodule.subtype_apply,hz,←map_add,ey] using high
  let S := univ.filter (fun z => f p+f (L z)=1)
  have bound : 2^d≤2*S.card := affine_bit_count (f p) (f.comp L) fat
  let pick (z:Cube d) : Cube d×F := (z,if f (x z)=b then 0 else 1)
  have inj : Function.Injective (fun z => a (pick z)) := fun _ _ e => congrArg Prod.fst (uniq e)
  have incl : S.image (fun z => a (pick z))⊆A.filter (fun v => f v=b) := by
    intro v' mem
    obtain ⟨w,hw,rfl⟩ := mem_image.mp mem
    refine mem_filter.mpr ⟨inA _,?_⟩
    by_cases hit : f (x w)=b
    · simp [pick,hit,a0]
    · have sum := congrArg f (eq w)
      simp only [map_add] at sum
      rw [(mem_filter.mp hw).2] at sum
      have other := (show ∀ u v b:F,u+v=1 → u≠b → v=b from by decide) _ _ _ sum hit
      simpa [pick,hit,a1] using other
  have c := card_le_card incl
  rw [card_image_of_injective _ inj] at c
  omega

open Green51LocalFlats Green51PairedTypes
variable {E:Type*} [AddCommGroup E] [Module F E] [DecidableEq E] [Fintype E]

/-- Distinct affine three-spaces in the double, counted by their point sets. -/
def family (A:Finset G) : Set (Set G) := {D | ∃ (p:G) (W:Submodule F G),
  Module.finrank F W=3 ∧ D=p +ᵥ (W:Set G) ∧ D⊆↑(A+A)}

omit [DecidableEq G] [Fintype G] [DecidableEq E] [Fintype E] in
private theorem image_coset (f:E →ₗ[F] G) (p:E) (W:Submodule F E) :
    (f '' (p +ᵥ (W:Set E)))=f p +ᵥ (W.map f:Set G) := by
  ext y
  constructor
  · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨f w,⟨_,hw,rfl⟩,(f.map_add _ _).symm⟩
  · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨p+w,⟨w,hw,rfl⟩,f.map_add _ _⟩

private theorem family_image (f:E →ₗ[F] G) (inj:Function.Injective f) (A:Finset E) :
    family (A.image f)=((Set.image f) '' family A) := by
  have dbl : A.image f+A.image f=(A+A).image f := by rw [image_add]
  ext D
  constructor
  · rintro ⟨p,W,rank,rfl,sub⟩
    have inrange {y} (hy:y∈p +ᵥ (W:Set G)) : y∈f.range := by
      obtain ⟨v,_,e⟩ := mem_image.mp (dbl ▸ sub hy)
      exact ⟨v,e⟩
    obtain ⟨a,ea⟩ := inrange (show p∈p +ᵥ (W:Set G) from ⟨0,W.zero_mem,add_zero _⟩)
    have filled : W≤f.range := by
      intro w hw
      obtain ⟨c,ec⟩ := inrange (show p+w∈p +ᵥ (W:Set G) from ⟨w,hw,rfl⟩)
      exact ⟨c-a,by rw [map_sub,ec,ea];abel⟩
    let V := W.comap f
    have same : V.map f=W := Submodule.map_comap_eq_self filled
    have image : f '' (a +ᵥ (V:Set E))=p +ᵥ (W:Set G) := by rw [image_coset,same,ea]
    refine ⟨_,⟨a,V,(V.equivMapOfInjective f inj).finrank_eq.trans (same ▸ rank),rfl,?_⟩,image⟩
    intro z hz
    have h := sub (image ▸ Set.mem_image_of_mem f hz)
    obtain ⟨x,hx,e⟩ := mem_image.mp (dbl ▸ h)
    exact inj e ▸ hx
  · rintro ⟨_,⟨p,W,rank,rfl,sub⟩,rfl⟩
    refine ⟨f p,W.map f,(W.equivMapOfInjective f inj).finrank_eq.symm.trans rank,image_coset _ _ _,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact dbl ▸ mem_image_of_mem f (sub hx)

theorem count_copy {A:Finset E} {B:Finset G} (copy:AffineCopy A B) :
    (family B).ncard=(family A).ncard := by
  obtain ⟨f,t,inj,rfl⟩ := copy
  have eq : A.image (fun x=>t+f x)=(A.image f).image (fun x=>t+x) := by
    simp only [image_image,Function.comp_def]
  have same : family ((A.image f).image (fun x=>t+x))=family (A.image f) := by
    unfold family
    rw [Green51PairedTypes.translated_double]
  rw [eq,same,family_image f inj,Set.ncard_image_of_injective _ inj.image_injective]

private def coordinate {m:ℕ} (i:Cube m) : Ambient m →ₗ[F] F :=
  (LinearMap.proj i).comp (LinearMap.fst F (Cube m→F) (F×Cube m))

private theorem few_ones {m:ℕ} (i:Cube m) :
    ((labels m).filter (fun x => coordinate i x=1)).card≤2 := by
  have sub : (labels m).filter (fun x => coordinate i x=1)⊆{leftPoint i,rightPoint i} := by
    intro x hx
    obtain ⟨raw,one⟩ := mem_filter.mp hx
    rcases mem_union.mp raw with h|h
    · obtain ⟨v,_,rfl⟩ := mem_image.mp h
      by_cases same:v=i
      · rw [same];exact mem_insert_self _ _
      · change (Pi.single v 1 : Cube m→F) i=1 at one
        simp [Ne.symm same] at one
    · obtain ⟨v,_,rfl⟩ := mem_image.mp h
      by_cases same:v=i
      · rw [same];exact mem_insert_of_mem (mem_singleton_self _)
      · change (Pi.single v 1 : Cube m→F) i=1 at one
        simp [Ne.symm same] at one
  exact (card_le_card sub).trans (card_le_two)

def vertical (m:ℕ) : Set (Ambient m) := Set.range (fun z:Cube m => ((0,1,z):Ambient m))

private theorem zero_row {m:ℕ} (y:Ambient m) (inside:y∈labels m+labels m) (row:y.1=0) :
    y=0 ∨ y∈vertical m := by
  have single {a b:Cube m} (e:(Pi.single a 1 : Cube m→F)+Pi.single b 1=0) : a=b := by
    by_contra n
    have h := congrFun e a
    simp [n] at h
  obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp inside
  rcases mem_union.mp ha with h|h <;> obtain ⟨i,_,rfl⟩ := mem_image.mp h <;>
    rcases mem_union.mp hb with h|h <;> obtain ⟨j,_,rfl⟩ := mem_image.mp h
  all_goals
    have ij := single ((congrArg Prod.fst eq).trans row)
    subst j
  · left;rw [←eq,ZModModule.add_self]
  · right;exact ⟨i,by rw [←eq];simp [leftPoint,rightPoint,Prod.mk_add_mk,ZModModule.add_self]⟩
  · right;exact ⟨i,by rw [←eq];simp [leftPoint,rightPoint,Prod.mk_add_mk,ZModModule.add_self]⟩
  · left;rw [←eq,ZModModule.add_self]

/-- Every affine flat of rank at least three in the universal paired model
lies inside the distinguished flat of vertical pair sums. -/
theorem universal_flat {m d:ℕ} (large:3≤d) (p:Ambient m) (W:Submodule F (Ambient m))
    (dim:Module.finrank F W=d) (inside:p +ᵥ (W:Set (Ambient m))⊆↑(labels m+labels m)) :
    p +ᵥ (W:Set (Ambient m)) ⊆ vertical m := by
  have avoid : ¬∃ V:Submodule F (Ambient m),Module.finrank F V=3 ∧ ∀ v∈V,v∈labels m+labels m := by
    rintro ⟨V,r,mem⟩
    have bound := Green51SparseDimensions.rank_without_relation _ (label_free m) V mem
    omega
  intro y hy
  have row : y.1=0 := by
    funext i
    by_contra ne
    have pos : y.1 i=1 := ((show ∀ a:F,a=0 ∨ a=1 from by decide) _).resolve_left ne
    have cost := hyperplane_cost large (labels m) avoid W dim p inside (coordinate i) hy pos 1
    have cap := few_ones i
    have eight := Nat.pow_le_pow_right (by decide : 0<2) large
    omega
  rcases zero_row y (inside hy) row with zero|done
  · obtain ⟨v,hv,e⟩ := (show ∃ v∈W,p+v=y from hy)
    rw [zero,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at e
    have hp : p∈W := e ▸ hv
    have mem (w) (hw:w∈W) : w∈labels m+labels m := inside
      ⟨p+w,W.add_mem hp hw,by change p+(p+w)=w;rw [←add_assoc,ZModModule.add_self,zero_add]⟩
    have bound := Green51SparseDimensions.rank_without_relation _ (label_free m) W mem
    omega
  · exact done

private theorem vertical_card (m:ℕ) : (vertical m).ncard=2^m := by
  have inj : Function.Injective (fun z:Cube m => ((0,1,z):Ambient m)) :=
    fun _ _ e => congrArg (fun x:Ambient m => x.2.2) e
  rw [vertical,Set.ncard_range_of_injective inj]
  simp [Cube,Nat.card_eq_fintype_card]

private theorem label_family : family (labels 3)={vertical 3} := by
  have unique {D} (h:D∈family (labels 3)) : D=vertical 3 := by
    obtain ⟨p,W,dim,rfl,sub⟩ := h
    apply Set.eq_of_subset_of_ncard_le (universal_flat (by decide) p W dim sub)
    rw [vertical_card,Set.ncard_eq_toFinset_card',flat_card,dim]
  obtain ⟨W,p,dim,sub⟩ := model_flat 3
  have existsD : p +ᵥ (W:Set (Ambient 3)) ∈family (labels 3) := ⟨p,W,dim,rfl,sub⟩
  ext D
  constructor
  · exact fun h => Set.mem_singleton_iff.mpr (unique h)
  · intro h
    rw [Set.mem_singleton_iff.mp h,←unique existsD]
    exact existsD

theorem count_large : (family largeModel).ncard=1 := by
  have copy : AffineCopy largeModel (labels 3) := by
    refine ⟨parity.ker.subtype,origin,Subtype.val_injective,?_⟩
    rw [largeModel,image_image,labels_eq]
    apply image_congr
    intro i _
    change origin+(label i+origin)=label i
    rw [add_left_comm,ZModModule.add_self,add_zero]
  rw [←count_copy copy,label_family,Set.ncard_singleton]

private theorem graph_family {D:Set (Target 4)} :
    D∈family (graph 4) ↔ ∃ t:Cube 4,t≠0 ∧ D=fiber t := by
  change (∃ (p:Target 4) (W:Submodule F (Target 4)),Module.finrank F W=3 ∧
      D=p +ᵥ (W:Set (Target 4)) ∧ D⊆↑(graph 4+graph 4)) ↔ _
  simpa only [show ∀ n:ℕ,n+1=4 ↔ n=3 from fun n => by omega] using largest_flats (by decide : 4≤4) D

private theorem count_graph : (family (graph 4)).ncard=15 := by
  simpa only [family,show ∀ n:ℕ,n+1=4 ↔ n=3 from fun n => by omega,show 2^4-1=15 from rfl] using
    number_of_largest_flats (by decide : 4≤4)

theorem small_to_graph : AffineCopy smallModel (graph 4) := by
  have contains : (family (graph 4)).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by rw [count_graph];decide)
  obtain ⟨D,p,W,rank,rfl,inside⟩ := contains
  have h : Witness (graph 4) := by
    refine ⟨?_,fun h => avoids_linear 4 ((Green51TenDimensions.flat_zero _).mp h),p,W,rank,inside⟩
    rw [graph,card_image_of_injective _ quad_inj,card_univ]
    simp [Cube]
  rcases of_witness h with big|small
  · have wrong := (count_copy big).symm.trans count_graph
    rw [count_large] at wrong;contradiction
  · exact small

theorem count_small : (family smallModel).ncard=15 :=
  (count_copy small_to_graph).symm.trans count_graph

/-- Every sixteen-label separation witness has one affine three-space in
affine dimension eleven, or fifteen in affine dimension ten. -/
theorem exact_count (A:Finset G) (h:Witness A) :
    (Module.finrank F (directions A)=11 ∧ (family A).ncard=1) ∨
    (Module.finrank F (directions A)=10 ∧ (family A).ncard=15) := by
  rcases of_witness h with big|small
  · left;rw [copy_rank big,directions_large,finrank_top,rank_large,count_copy big,count_large];exact ⟨rfl,rfl⟩
  · right;rw [copy_rank small,directions_small,finrank_top,rank_small,count_copy small,count_small];exact ⟨rfl,rfl⟩

/-- Every nonzero pair sum belongs to exactly one affine three-space. -/
def Partitions (A:Finset G) : Prop :=
  ∀ x∈A+A,x≠0 → ∃! D, D∈family A ∧ x∈D

private theorem through_image (f:E →ₗ[F] G) (inj:Function.Injective f) (A:Finset E) (x:E) :
    (∃! D,D∈family (A.image f) ∧ f x∈D) ↔ (∃! S,S∈family A ∧ x∈S) := by
  have mem {S:Set E} : f x∈f '' S ↔ x∈S := inj.mem_set_image
  rw [family_image f inj]
  constructor
  · rintro ⟨D,⟨⟨S,hS,rfl⟩,hx⟩,only⟩
    refine ⟨S,⟨hS,mem.mp hx⟩,?_⟩
    rintro U ⟨hU,hx⟩
    exact inj.image_injective (only (f '' U) ⟨Set.mem_image_of_mem _ hU,mem.mpr hx⟩)
  · rintro ⟨S,⟨hS,hx⟩,only⟩
    refine ⟨f '' S,⟨Set.mem_image_of_mem _ hS,mem.mpr hx⟩,?_⟩
    rintro _ ⟨⟨U,hU,rfl⟩,hh⟩
    exact congrArg (Set.image f) (only U ⟨hU,mem.mp hh⟩)

private theorem partitions_copy {A:Finset E} {B:Finset G} (copy:AffineCopy A B) :
    Partitions B ↔ Partitions A := by
  obtain ⟨f,t,inj,rfl⟩ := copy
  have eq : A.image (fun x=>t+f x)=(A.image f).image (fun x=>t+x) := by
    simp only [image_image,Function.comp_def]
  have same : family ((A.image f).image (fun x=>t+x))=family (A.image f) := by
    unfold family;rw [translated_double]
  simp only [Partitions,eq,translated_double,same,←image_add]
  constructor
  · intro original x hx nz
    apply (through_image f inj A x).mp
    exact original (f x) (mem_image_of_mem f hx) (fun h => nz (inj (h.trans f.map_zero.symm)))
  · intro original y hy nz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact (through_image f inj A x).mpr (original x hx (fun h => nz (h ▸ f.map_zero)))

private theorem small_partitions : Partitions smallModel := by
  have known : Partitions (graph 4) := by
    intro y hy nz
    let t := horizontal 4 y
    have hit := (fiber_iff t y).mpr ⟨hy,rfl⟩
    have nonzero : t≠0 := by
      intro eq;rw [eq,fiber_zero] at hit;exact nz (Set.mem_singleton_iff.mp hit)
    refine ⟨fiber t,⟨graph_family.mpr ⟨_,nonzero,rfl⟩,hit⟩,?_⟩
    rintro D ⟨valid,mem⟩
    obtain ⟨s,_,rfl⟩ := graph_family.mp valid
    exact congrArg fiber ((fiber_iff s y).mp mem).2.symm
  exact (partitions_copy small_to_graph).mp known

theorem unique_through_nonzero (A:Finset G) (w:Witness A)
    (rank:Module.finrank F (directions A)=10) : Partitions A := by
  rcases of_witness w with big|small
  · rw [copy_rank big,directions_large,finrank_top,rank_large] at rank
    contradiction
  · exact (partitions_copy small).mpr small_partitions

end Green51WitnessIncidence


#print axioms Green51WitnessIncidence.hyperplane_cost
#print axioms Green51WitnessIncidence.count_copy
#print axioms Green51WitnessIncidence.universal_flat
#print axioms Green51WitnessIncidence.count_large
#print axioms Green51WitnessIncidence.small_to_graph
#print axioms Green51WitnessIncidence.count_small
#print axioms Green51WitnessIncidence.exact_count
#print axioms Green51WitnessIncidence.unique_through_nonzero
