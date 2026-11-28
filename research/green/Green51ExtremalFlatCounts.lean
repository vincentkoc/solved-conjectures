import Green51OctadFlats

/-! # Affine three-space incidence in extremal twenty-four-label doubles -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PairedTypes Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51PerfectColumns
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem pair_inj {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    {S T:Finset V} (sa:S⊆A) (ta:T⊆A) (s2:S.card=2) (t2:T.card=2)
    (sum:syndrome S=syndrome T) : S=T := by
  have small:=card_union_le S T
  have outside:¬A⊆S∪T := fun sub => by have le:=card_le_card sub; omega
  obtain ⟨a,ha,notin⟩:=not_subset.mp outside
  obtain ⟨hs,ht⟩:=notMem_union.mp notin
  have mem {U:Finset V} (ua:U⊆A) (u2:U.card=2) (un:a∉U) : insert a U∈oddSets A :=
    mem_union_right _ (mem_powersetCard.mpr ⟨insert_subset ha ua,by rw [card_insert_of_notMem un,u2]⟩)
  have inj : Set.InjOn syndrome ↑(oddSets A) := Green51SparseDimensions.odd_sum_inj A
    (by omega) (fun h => avoid ((flat_zero A).mpr h))
  have eq := inj (mem sa s2 hs) (mem ta t2 ht) (by
    change (∑x∈insert a S,x)=∑x∈insert a T,x
    rw [sum_insert hs,sum_insert ht];exact congrArg (a+·) sum)
  simpa only [erase_insert hs,erase_insert ht] using congrArg (fun R:Finset V => R.erase a) eq

private theorem common_double {A B C:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ba:B⊆A) (ca:C⊆A) (non:(B∩C).Nonempty) :
    (B+B)∩(C+C)⊆(B∩C)+(B∩C) := by
  intro v hv
  by_cases z:v=0
  · obtain ⟨x,h⟩:=non
    simpa only [z,ZModModule.add_self] using add_mem_add h h
  obtain ⟨b,hb,e,he,be⟩:=mem_add.mp (mem_inter.mp hv).1
  obtain ⟨c,hc,f,hf,cf⟩:=mem_add.mp (mem_inter.mp hv).2
  have bne:b≠e := fun eq => z (be.symm.trans (eq ▸ ZModModule.add_self e))
  have cne:c≠f := fun eq => z (cf.symm.trans (eq ▸ ZModModule.add_self f))
  have pairs : ({b,e}:Finset V)={c,f} := pair_inj size avoid
    (insert_subset (ba hb) (singleton_subset_iff.mpr (ba he)))
    (insert_subset (ca hc) (singleton_subset_iff.mpr (ca hf)))
    (card_pair bne) (card_pair cne) (by simpa only [syndrome,sum_pair bne,sum_pair cne] using be.trans cf.symm)
  have sub : ({b,e}:Finset V)⊆C := pairs ▸ insert_subset hc (singleton_subset_iff.mpr hf)
  exact be ▸ add_mem_add (mem_inter.mpr ⟨hb,sub (mem_insert_self ..)⟩)
    (mem_inter.mpr ⟨he,sub (mem_insert_of_mem (mem_singleton_self _))⟩)

private noncomputable def flats (A:Finset V) : Finset (Set V) := (family A).toFinset

private theorem parts {A U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) (ua:U⊆A) :
    ((octadFamily A).filter (U⊆·)).biUnion (fun O => flats (A\O))=flats (A\U) := by
  classical
  ext D
  constructor
  · intro h
    obtain ⟨O,hO,mem⟩:=mem_biUnion.mp h
    obtain ⟨p,W,rank,eq,sub⟩:= (Set.mem_toFinset.mp mem : D∈family (A\O))
    have keep:A\O⊆A\U := fun x hx => mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1,
      fun h => (mem_sdiff.mp hx).2 ((mem_filter.mp hO).2 h)⟩
    exact Set.mem_toFinset.mpr ⟨p,W,rank,eq,fun _ hx => add_subset_add keep keep (sub hx)⟩
  · intro h
    obtain ⟨p,W,d,eq,inside⟩:=(Set.mem_toFinset.mp h : D∈family (A\U))
    have avoids:¬FlatAt (A\U) 0 := fun ⟨L,r,inside'⟩=>avoid ⟨L,r,fun v hv=>
      add_subset_add sdiff_subset sdiff_subset (inside' hv)⟩
    obtain ⟨B,localSub,sz,zero,retains⟩:=sixteen_relation_for avoids p W d (eq ▸ inside)
    have sub:B⊆A:=localSub.trans sdiff_subset
    have oct : A\B∈octadFamily A := by
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨sdiff_subset,by rw [card_sdiff_of_subset sub,size,sz]⟩,?_⟩
      have sum:=sum_sdiff sub (f:=id)
      change syndrome (A\B)+(∑x∈B,x)=syndrome A at sum
      simpa only [zero,add_zero,full_sum size avoid] using sum
    apply mem_biUnion.mpr
    refine ⟨A\B,mem_filter.mpr ⟨oct,fun x hx => mem_sdiff.mpr ⟨ua hx,
      fun h => (mem_sdiff.mp (localSub h)).2 hx⟩⟩,?_⟩
    have back : A\(A\B)=B := by
      ext x
      simp only [mem_sdiff]
      constructor <;> intro hx
      · by_contra notB;exact hx.2 ⟨hx.1,notB⟩
      · exact ⟨sub hx,fun e => e.2 hx⟩
    rw [back]
    exact Set.mem_toFinset.mpr ⟨p,W,d,eq,eq ▸ retains⟩

private theorem disjoint_parts {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) :
    (octadFamily A:Set (Finset V)).PairwiseDisjoint (fun O => flats (A\O)) := by
  classical
  intro O hO U hU different
  apply Finset.disjoint_left.mpr
  intro D inO inU
  obtain ⟨oa,oc⟩:=mem_powersetCard.mp (mem_filter.mp hO).1
  obtain ⟨ua,uc⟩:=mem_powersetCard.mp (mem_filter.mp hU).1
  let B:=A\O
  let C:=A\U
  have bc:B.card=16 := by simp [B,card_sdiff_of_subset oa,size,oc]
  have cc:C.card=16 := by simp [C,card_sdiff_of_subset ua,size,uc]
  have subB:B⊆A:=sdiff_subset
  have subC:C⊆A:=sdiff_subset
  have cap:=card_le_card (union_subset subB subC)
  have count:=card_inter_add_card_union B C
  have non:(B∩C).Nonempty:=card_pos.mp (by omega)
  obtain ⟨p,W,dim,eq,inside⟩ := (Set.mem_toFinset.mp inO : D∈family B)
  obtain ⟨_,_,_,_,inside'⟩ := (Set.mem_toFinset.mp inU : D∈family C)
  have keep : p +ᵥ (W:Set V)⊆↑((B∩C)+(B∩C)) := by
    rw [←eq]
    exact fun x hx => common_double size avoid subB subC non (mem_inter.mpr ⟨inside hx,inside' hx⟩)
  have avoidBC : ¬∃ V':Submodule F V,Module.finrank F V'=3 ∧ ∀x∈V',x∈(B∩C)+(B∩C) := by
    rintro ⟨V',dim',h⟩
    have sub : B∩C⊆A:=inter_subset_left.trans subB
    exact avoid ((flat_zero A).mpr ⟨V',dim',fun x hx => add_subset_add sub sub (h x hx)⟩)
  have cost:=Green51AffineMatchings.affine_flat_cost (B∩C) avoidBC W p keep dim.ge
  rw [dim] at cost
  have eqBC:B=C := (eq_of_subset_of_card_le inter_subset_left (by omega) : B∩C=B).symm.trans
      (eq_of_subset_of_card_le inter_subset_right (by omega))
  apply different
  ext x
  have same := Finset.ext_iff.mp eqBC x
  change x∈A\O ↔ x∈A\U at same
  simp only [mem_sdiff] at same
  constructor
  · intro hx; by_contra notU; exact (same.mpr ⟨oa hx,notU⟩).2 hx
  · intro hx; by_contra notO; exact (same.mp ⟨ua hx,notO⟩).2 hx

/-- Deleting labels retains fifteen affine three-spaces for each zero-sum octad
containing the deleted set. -/
theorem deleted_flat_count {A U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) (ua:U⊆A) :
    (family (A\U)).ncard=((octadFamily A).filter (U⊆·)).card*15 := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  change (flats (A\U)).card=_
  rw [←parts size avoid ua,card_biUnion]
  swap
  · intro x hx y hy ne; exact disjoint_parts size avoid (mem_filter.mp hx).1 (mem_filter.mp hy).1 ne
  calc
    _ = ∑ _O∈(octadFamily A).filter (U⊆·),(15:ℕ) := by
      apply sum_congr rfl
      intro O ho
      exact (Set.ncard_eq_toFinset_card' (family (A\O))).symm.trans (complement_fifteen size avoid (mem_filter.mp ho).1).1
    _ = _ := by simp

/-- Every extremal twenty-four-label set has the same number of affine
three-spaces in its double. The flats are counted by their point sets. -/
theorem eleven_thousand_flats {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) :
    (family A).ncard=11385 := by
  simpa [octad_count size avoid] using deleted_flat_count size avoid (empty_subset A)

private theorem avoiding_pair_count {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    {x y:V} (hx:x∈A) (hy:y∈A) (ne:x≠y) :
    ((octadFamily A).filter fun O => x∉O ∧ y∉O).card=330 := by
  classical
  let H:=octadFamily A
  let X:=H.filter (x∈·)
  let Y:=H.filter (y∈·)
  have xsize : X.card=253 := octads_through_label size avoid hx
  have ysize : Y.card=253 := octads_through_label size avoid hy
  have joint : X∩Y=H.filter ({x,y}⊆·) := by
    ext O; simp only [X,Y,mem_inter,mem_filter,insert_subset_iff,singleton_subset_iff];tauto
  have both : (X∩Y).card=77 := by
    rw [joint]
    have h:=flags size avoid {x,y} (insert_subset hx (singleton_subset_iff.mpr hy))
      (by rw [card_pair ne];decide)
    rw [card_pair ne] at h
    change 20*(H.filter ({x,y}⊆·)).card=1540 at h
    omega
  have diff : H.filter (fun O => x∉O ∧ y∉O)=H\(X∪Y) := by
    ext O; simp only [X,Y,mem_sdiff,mem_union,mem_filter];tauto
  change (H.filter _).card=330
  rw [diff,card_sdiff_of_subset (union_subset (filter_subset ..) (filter_subset ..))]
  have total : H.card=759 := octad_count size avoid
  have eq:=card_inter_add_card_union X Y
  have together:(X∪Y).card=429 := by omega
  change H.card-(X∪Y).card=330
  rw [total,together]

/-- A surviving pair sum lies on one affine three-space for each octad that
contains the deleted labels and avoids the pair. -/
theorem deleted_point_count {A U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) (ua:U⊆A)
    {x y:V} (hx:x∈A) (hy:y∈A) (ne:x≠y) :
    ({D:Set V | D∈family (A\U) ∧ x+y∈D}:Set (Set V)).ncard=
      ((octadFamily A).filter (fun O=>U⊆O ∧ x∉O ∧ y∉O)).card := by
  classical
  let v:=x+y
  have xy:x+y=v:=rfl
  have nz:v≠0 := fun z=>ne (add_right_cancel (z.trans (ZModModule.add_self y).symm))
  have localCount (O:Finset V) (ho:O∈octadFamily A) :
      ((flats (A\O)).filter (v∈·)).card=if x∉O ∧ y∉O then 1 else 0 := by
    let B:=A\O
    by_cases cond:x∉O ∧ y∉O
    · rw [if_pos cond]
      have vb : v∈B+B := xy ▸ add_mem_add (mem_sdiff.mpr ⟨hx,cond.1⟩) (mem_sdiff.mpr ⟨hy,cond.2⟩)
      obtain ⟨D,⟨inside,mem⟩,uniq⟩ := (complement_fifteen size avoid ho).2 v vb nz
      apply card_eq_one.mpr
      refine ⟨D,?_⟩
      ext E
      constructor
      · intro h
        obtain ⟨inE,ve⟩:=mem_filter.mp h
        exact mem_singleton.mpr (uniq E ⟨Set.mem_toFinset.mp inE,ve⟩)
      · rintro h
        have := mem_singleton.mp h; subst E
        exact mem_filter.mpr ⟨Set.mem_toFinset.mpr inside,mem⟩
    · rw [if_neg cond,card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro D hd
      obtain ⟨dd,vd⟩:=mem_filter.mp hd
      obtain ⟨_,_,_,_,ins⟩ := (Set.mem_toFinset.mp dd : D∈family B)
      obtain ⟨a,ha,b,hb,ab⟩:=mem_add.mp (ins vd)
      have alt : a≠b := fun e => nz (ab.symm.trans (e ▸ ZModModule.add_self b))
      have eq : ({x,y}:Finset V)={a,b} := pair_inj size avoid
        (insert_subset hx (singleton_subset_iff.mpr hy))
        (insert_subset (mem_sdiff.mp ha).1 (singleton_subset_iff.mpr (mem_sdiff.mp hb).1))
        (card_pair ne) (card_pair alt) (by simpa only [syndrome,sum_pair ne,sum_pair alt] using xy.trans ab.symm)
      have sub : ({x,y}:Finset V)⊆B := eq ▸ insert_subset ha (singleton_subset_iff.mpr hb)
      exact cond ⟨(mem_sdiff.mp (sub (mem_insert_self ..))).2,
        (mem_sdiff.mp (sub (mem_insert_of_mem (mem_singleton_self _)))).2⟩
  have dis : (((octadFamily A).filter (U⊆·)):Set (Finset V)).PairwiseDisjoint
      (fun O => (flats (A\O)).filter (v∈·)) := by
    intro O ho U hu neq
    exact (disjoint_parts size avoid (mem_filter.mp ho).1 (mem_filter.mp hu).1 neq).mono (filter_subset ..) (filter_subset ..)
  have eq : ({D:Set V | D∈family (A\U) ∧ v∈D}:Set (Set V)).toFinset=(flats (A\U)).filter (v∈·) := by
    ext; simp [flats]
  rw [Set.ncard_eq_toFinset_card',eq,←parts size avoid ua,filter_biUnion,card_biUnion dis]
  calc
    _ = ∑O∈(octadFamily A).filter (U⊆·),if x∉O ∧ y∉O then (1:ℕ) else 0 := sum_congr rfl fun O h => localCount O (mem_filter.mp h).1
    _ = _ := by
      rw [sum_boole,filter_filter]
      rfl

/-- Every nonzero point of an extremal double belongs to exactly 330 of its
affine three-spaces. -/
theorem through_nonzero {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    {v:V} (hv:v∈A+A) (nz:v≠0) :
    ({D:Set V | D∈family A ∧ v∈D}:Set (Set V)).ncard=330 := by
  classical
  obtain ⟨x,hx,y,hy,xy⟩:=mem_add.mp hv
  have ne : x≠y := fun e => nz (xy.symm.trans (e ▸ ZModModule.add_self y))
  have count:=deleted_point_count (U:=∅) size avoid (empty_subset A) hx hy ne
  simpa [xy,avoiding_pair_count size avoid hx hy ne] using count

end Green51PerfectColumns
#print axioms Green51PerfectColumns.deleted_flat_count
#print axioms Green51PerfectColumns.deleted_point_count
#print axioms Green51PerfectColumns.eleven_thousand_flats

#print axioms Green51PerfectColumns.through_nonzero
