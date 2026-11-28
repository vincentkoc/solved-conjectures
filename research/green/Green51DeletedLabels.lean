import Green51ExtremalFlatCounts
import Green51MissingLabel

/-! # Affine three-spaces after deletion from an extremal double -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51WitnessIncidence Green51PerfectColumns
open scoped Classical Pointwise
namespace Green51DeletedLabels
local notation "V" => Cube 11

/-- Number of octads containing specified labels, for at most five labels. -/
def multiplicity (i:ℕ) : ℕ := (24-i).choose (5-i)/(8-i).choose (5-i)

private theorem flags_value {A U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ua:U⊆A) (small:U.card≤5) : ((octadFamily A).filter (U⊆·)).card=multiplicity U.card := by
  have eq:=flags size avoid U ua small
  exact (Nat.div_eq_of_eq_mul_left (Nat.choose_pos (by omega))
    (eq.symm.trans (Nat.mul_comm ..))).symm

/-- Up to five deletions, the number of flats depends only on the number of deleted labels. -/
theorem flat_count_of_at_most_five_deletions {A U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ua:U⊆A) (small:U.card≤5) : (family (A\U)).ncard=15*multiplicity U.card := by
  rw [deleted_flat_count size avoid ua,flags_value size avoid ua small,Nat.mul_comm]

/-- For up to three deletions, each remaining nonzero pair sum has the same flat count. -/
theorem point_count_of_at_most_three_deletions {A U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ua:U⊆A) (small:U.card≤3) {x y:V} (hx:x∈A\U) (hy:y∈A\U) (ne:x≠y) :
    ({D:Set V | D∈family (A\U) ∧ x+y∈D}:Set (Set V)).ncard=
      multiplicity U.card+multiplicity (U.card+2)-2*multiplicity (U.card+1) := by
  classical
  obtain ⟨xa,xu⟩:=mem_sdiff.mp hx
  obtain ⟨ya,yu⟩:=mem_sdiff.mp hy
  rw [deleted_point_count size avoid ua xa ya ne]
  let H:=(octadFamily A).filter (U⊆·)
  let X:=H.filter (x∈·)
  let Y:=H.filter (y∈·)
  have count : H.card=multiplicity U.card:=flags_value size avoid ua (by omega)
  have one (a:V) (ha:a∈A) (au:a∉U) :
      (H.filter (a∈·)).card=multiplicity (U.card+1) := by
    have eq : H.filter (a∈·)=(octadFamily A).filter (insert a U⊆·) := by
      ext O; simp only [H,mem_filter,insert_subset_iff];tauto
    rw [eq,flags_value size avoid (insert_subset ha ua) (by rw [card_insert_of_notMem au];omega),
      card_insert_of_notMem au]
  have xc : X.card=multiplicity (U.card+1):=one x xa xu
  have yc : Y.card=multiplicity (U.card+1):=one y ya yu
  have eq : X∩Y=(octadFamily A).filter (insert x (insert y U)⊆·) := by
    ext O;simp only [X,Y,H,mem_inter,mem_filter,insert_subset_iff];tauto
  have sz : (insert x (insert y U)).card=U.card+2 := by
    rw [card_insert_of_notMem (by simpa using And.intro ne xu),card_insert_of_notMem yu]
  have both : (X∩Y).card=multiplicity (U.card+2) := by
    rw [eq,flags_value size avoid (insert_subset xa (insert_subset ya ua)) (by omega),sz]
  have diff : (octadFamily A).filter (fun O => U⊆O ∧ x∉O ∧ y∉O)=H\(X∪Y) := by
    ext O;simp only [H,X,Y,mem_filter,mem_sdiff,mem_union];tauto
  have balance:=card_inter_add_card_union X Y
  rw [diff,card_sdiff_of_subset (union_subset (filter_subset ..) (filter_subset ..))]
  change H.card-(X∪Y).card=multiplicity U.card+multiplicity (U.card+2)-2*multiplicity (U.card+1)
  omega

/-- Every avoiding twenty-three-label set has 3,795 affine three-spaces in its double,
and each nonzero point lies on 120. -/
theorem twenty_three {A:Finset V} (size:A.card=23) (avoid:¬FlatAt A 0) :
    (family A).ncard=3795 ∧ ∀v∈A+A,v≠0 →
      ({D:Set V | D∈family A ∧ v∈D}:Set (Set V)).ncard=120 := by
  obtain ⟨fresh,safe,_⟩:=Green51MissingLabel.extension size avoid
  let p:=syndrome A
  let B:=insert p A
  have bs:B.card=24:=by dsimp only [B]; rw [card_insert_of_notMem fresh,size]
  have sub:({p}:Finset V)⊆B:=singleton_subset_iff.mpr (mem_insert_self ..)
  have back:B\{p}=A:=by rw [sdiff_singleton_eq_erase,erase_insert fresh]
  constructor
  · have t:=flat_count_of_at_most_five_deletions bs safe sub (by simp)
    rw [back,card_singleton] at t
    exact t
  · intro v hv nz
    obtain ⟨x,hx,y,hy,xy⟩:=mem_add.mp hv
    have diff:x≠y:=fun e=>nz (xy.symm.trans (e ▸ ZModModule.add_self y))
    have t:=point_count_of_at_most_three_deletions bs safe sub (by simp) (back ▸ hx) (back ▸ hy) diff
    rw [back,xy,card_singleton] at t
    exact t

/-- The seven-label subsets with the same sum as the whole set form a Steiner
system on every avoiding twenty-three-label set. -/
theorem unique_heptad {A:Finset V} (size:A.card=23) (avoid:¬FlatAt A 0)
    (T:Finset V) (ta:T⊆A) (four:T.card=4) :
    ∃!H:Finset V,H⊆A ∧ H.card=7 ∧ syndrome H=syndrome A ∧ T⊆H := by
  classical
  obtain ⟨fresh,safe,_⟩:=Green51MissingLabel.extension size avoid
  let p:=syndrome A
  let B:=insert p A
  have bs:B.card=24 := by dsimp only [B];rw [card_insert_of_notMem fresh,size]
  have pt:p∉T:=fun ht=>fresh (ta ht)
  obtain ⟨O,⟨ho,sub⟩,unique⟩:=unique_octad bs safe (insert p T)
    (insert_subset_insert p ta) (by rw [card_insert_of_notMem pt,four])
  obtain ⟨oa,oz⟩:=mem_powersetCard.mp (mem_filter.mp ho).1
  have zero:= (mem_filter.mp ho).2
  have po:p∈O:=sub (mem_insert_self ..)
  have small:=card_erase_add_one po
  have z:=O.add_sum_erase id po
  change p+syndrome (O.erase p)=syndrome O at z
  refine ⟨O.erase p,⟨?_,by omega,add_left_cancel (z.trans (zero.trans (ZModModule.add_self p).symm)),?_⟩,?_⟩
  · intro x hx
    exact (mem_insert.mp (oa (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1
  · intro x hx
    exact mem_erase.mpr ⟨fun e=>pt (e ▸ hx),sub (mem_insert_of_mem hx)⟩
  · rintro H ⟨ha,hz,hs,th⟩
    have ph:p∉H:=fun h=>fresh (ha h)
    have oct:insert p H∈octadFamily B := by
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset_insert p ha,?_⟩,?_⟩
      · rw [card_insert_of_notMem ph,hz]
      · change (∑x∈insert p H,x)=0
        rw [sum_insert ph]
        change p+syndrome H=0
        rw [hs];exact ZModModule.add_self p
    have eq:=unique (insert p H) ⟨oct,insert_subset_insert p th⟩
    simpa only [erase_insert ph] using congrArg (fun X:Finset V=>X.erase p) eq

end Green51DeletedLabels
#print axioms Green51DeletedLabels.flat_count_of_at_most_five_deletions
#print axioms Green51DeletedLabels.point_count_of_at_most_three_deletions
#print axioms Green51DeletedLabels.twenty_three

#print axioms Green51DeletedLabels.unique_heptad
