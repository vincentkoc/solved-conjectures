import Green51PermutedChords

/-! # Projection of a largest affine flat in a paired quadratic graph -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise symmDiff
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

def left (W:Submodule F (E n)) : W →ₗ[F] Target n := (LinearMap.fst F _ _).comp W.subtype
def verticalMap (W:Submodule F (E n)) : (left W).ker →ₗ[F] V n :=
  ((LinearMap.snd F _ _).comp W.subtype).comp (left W).ker.subtype
def vertical (W:Submodule F (E n)) := (verticalMap W).range
theorem verticalMap_inj (W:Submodule F (E n)) : Function.Injective (verticalMap W) := by
  intro x y h
  apply Subtype.ext;apply Subtype.ext
  exact Prod.ext (x.property.trans y.property.symm) h
theorem vertical_rank (W:Submodule F (E n)) :
    Module.finrank F (left W).range+Module.finrank F (vertical W)=Module.finrank F W := by
  rw [vertical,(verticalMap W).finrank_range_of_inj (verticalMap_inj W)]
  exact (left W).finrank_range_add_finrank_ker
theorem mem_vertical (W:Submodule F (E n)) (v:V n) : v∈vertical W ↔ (0,v)∈W := by
  constructor
  · rintro ⟨x,rfl⟩
    have eq : ((0,verticalMap W x):E n)=x.val.val := Prod.ext x.property.symm rfl
    rw [eq];exact x.val.property
  · intro h
    exact ⟨⟨⟨(0,v),h⟩,rfl⟩,rfl⟩

def baseFlat (P:E n) (W:Submodule F (E n)) := P.1 +ᵥ ((left W).range:Set (Target n))
theorem mem_baseFlat (P:E n) (W:Submodule F (E n)) (y:Target n) :
    y∈baseFlat P W ↔ ∃ v:V n,(y,v)∈P +ᵥ (W:Set (E n)) := by
  constructor
  · rintro ⟨v,⟨w,rfl⟩,rfl⟩
    exact ⟨P.2+w.val.2,w,w.property,rfl⟩
  · rintro ⟨v,w,hw,e⟩
    exact ⟨w.1,⟨⟨w,hw⟩,rfl⟩,congrArg Prod.fst e⟩

theorem vertical_le_chord (f:Cube n→Cube n) (b:Cube n→V n)
    (P:E n) (W:Submodule F (E n)) (inside:P +ᵥ (W:Set (E n))⊆↑(labels f b+labels f b))
    {x y:Cube n} (ne:x≠y) (h:quad x+quad y∈baseFlat P W) : vertical W≤pairPlane f x y := by
  obtain ⟨v,hv⟩:=(mem_baseFlat _ _ _).mp h
  intro k hk
  have add : (quad x+quad y,v+k)∈P +ᵥ (W:Set (E n)) := by
    obtain ⟨w,hw,e⟩:=hv
    refine ⟨w+(0,k),W.add_mem hw ((mem_vertical _ _).mp hk),?_⟩
    change P+(w+(0,k))=_
    rw [←add_assoc,show P+w=(quad x+quad y,v) from e]
    simp
  have j:=chord_difference f b ne (inside hv) (inside add)
  rwa [←add_assoc,ZModModule.add_self,zero_add] at j

theorem projected_subset (f:Cube n→Cube n) (b:Cube n→V n)
    (P:E n) (W:Submodule F (E n)) (inside:P +ᵥ (W:Set (E n))⊆↑(labels f b+labels f b)) :
    baseFlat P W⊆↑(graph n+graph n) := by
  intro z hz
  obtain ⟨v,hv⟩:=(mem_baseFlat _ _ _).mp hz
  obtain ⟨p,hp,q,hq,e⟩:=mem_add.mp (inside hv)
  obtain ⟨x,s,rfl⟩:=(mem_labels _ _ _).mp hp
  obtain ⟨y,t,rfl⟩:=(mem_labels _ _ _).mp hq
  rw [←(show quad x+quad y=z from congrArg Prod.fst e)]
  exact add_mem_add (mem_image_of_mem quad (mem_univ _)) (mem_image_of_mem quad (mem_univ _))

theorem ranks_of_nonvertical (large:4≤n) (f:Cube n→Cube n) (inj:Function.Injective f)
    (b:Cube n→V n) (P:E n) (W:Submodule F (E n)) (dim:Module.finrank F W=n)
    (inside:P +ᵥ (W:Set (E n))⊆↑(labels f b+labels f b))
    (nonzero:∃ z∈baseFlat P W,z≠0) :
    Module.finrank F (vertical W)=1 ∧ Module.finrank F (left W).range+1=n ∧
    ∃ t:Cube n,t≠0 ∧ baseFlat P W=fiber t := by
  have sub:=projected_subset f b P W inside
  have chord {z:Target n} (mem:z∈baseFlat P W) (nz:z≠0) :
      ∃ x y:Cube n,x≠y ∧ quad x+quad y=z := by
    obtain ⟨a,ha,b',hb,e⟩:=mem_add.mp (sub mem)
    obtain ⟨x,_,rfl⟩:=mem_image.mp ha
    obtain ⟨y,_,rfl⟩:=mem_image.mp hb
    refine ⟨x,y,?_,e⟩
    rintro rfl
    exact nz (e.symm.trans (ZModModule.add_self _))
  obtain ⟨z,hz,zn⟩:=nonzero
  obtain ⟨x,y,ne,rfl⟩:=chord hz zn
  have K:=vertical_le_chord f b P W inside ne hz
  have low:Module.finrank F (vertical W)≤2 := (Submodule.finrank_mono K).trans (pairPlane_rank _ _ _)
  have ranks:=vertical_rank W
  have basecard : (baseFlat P W).toFinset.card=2^(Module.finrank F (left W).range) := flat_card _ _
  have small:Module.finrank F (vertical W)≤1 := by
    by_contra! big
    have same:=Submodule.eq_of_le_of_finrank_le K ((pairPlane_rank _ _ _).trans big)
    have few : (baseFlat P W).toFinset ⊆ ({0,quad x+quad y}:Finset _) := by
      intro z mem
      rw [Set.mem_toFinset] at mem
      by_cases z0:z=0
      · simp [z0]
      obtain ⟨c,d,cd,rfl⟩:=chord mem z0
      have eq:=Submodule.eq_of_le_of_finrank_le (vertical_le_chord f b P W inside cd mem)
        ((pairPlane_rank _ _ _).trans big)
      have hit:=plane_determines_chord f inj cd (eq.symm.trans same)
      simp [hit]
    have count:=(card_le_card few).trans Finset.card_le_two
    rw [basecard] at count
    have big':2≤Module.finrank F (left W).range := by omega
    have := Nat.pow_le_pow_right (by decide : 0<2) big'
    omega
  have three : 3≤Module.finrank F (left W).range := by omega
  let t:=horizontal n P.1
  have contained:baseFlat P W⊆fiber t := (flat_iff_single_fiber P.1 (left W).range three).mp sub
  have tn:t≠0 := by
    intro h
    have e:=contained hz
    rw [h,fiber_zero,Set.mem_singleton_iff] at e
    exact zn e
  have count:=card_le_card (Set.toFinset_subset_toFinset.mpr contained)
  rw [basecard,fiber,flat_card] at count
  have le:=(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp count
  have fd:=fiber_dimension tn
  have eq:Module.finrank F (left W).range=Module.finrank F (polar t).range := by omega
  refine ⟨by omega,by omega,t,tn,Set.toFinset_inj.mp (eq_of_subset_of_card_le (Set.toFinset_subset_toFinset.mpr contained) ?_)⟩
  rw [basecard,fiber,flat_card,eq]

end Green51PermutedPairs

#print axioms Green51PermutedPairs.vertical_rank
#print axioms Green51PermutedPairs.ranks_of_nonvertical
