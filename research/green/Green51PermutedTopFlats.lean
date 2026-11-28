import Green51PermutedProjection

/-! # Constant derivatives characterize additional affine flats -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise symmDiff
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

private theorem even_member (f:Cube n→Cube n) (x y:Cube n) {v:V n}
    (nonzero:v≠0) (even:v.1=0) (mem:v∈pairPlane f x y) : v.2=f x+f y := by
  obtain ⟨s,t,e⟩:=(mem_pairPlane _ _ _ _).mp mem
  rcases (show ∀ v:F,v=0 ∨ v=1 from by decide) s with rfl|rfl <;>
    rcases (show ∀ v:F,v=0 ∨ v=1 from by decide) t with rfl|rfl <;>
    simp only [zero_smul,one_smul,zero_add,add_zero] at e
  · exact False.elim (nonzero e)
  · exact False.elim (zero_ne_one (even.symm.trans (congrArg Prod.fst e)))
  · exact False.elim (zero_ne_one (even.symm.trans (congrArg Prod.fst e)))
  · exact congrArg Prod.snd e

theorem constant_derivative (large:4≤n) (f:Cube n ≃ Cube n) (b:Cube n→V n)
    (P:E n) (W:Submodule F (E n)) (dim:Module.finrank F W=n)
    (inside:P +ᵥ (W:Set (E n))⊆↑(labels f b+labels f b))
    (nonzero:∃ z∈baseFlat P W,z≠0) :
    ∃ t:Cube n,t≠0 ∧ baseFlat P W=fiber t ∧ ∀ x:Cube n, f x+f (x+t)=f 0+f t := by
  obtain ⟨kdim,_,t,tn,eq⟩:=ranks_of_nonvertical large f f.injective b P W dim inside nonzero
  obtain ⟨k,mem,kn⟩:∃ k∈vertical W,k≠0 := by
    by_contra! h
    have zero:vertical W=⊥ := (Submodule.eq_bot_iff _).mpr h
    rw [zero,finrank_bot] at kdim
    omega
  have common (x:Cube n) : k∈pairPlane f x (x+t) := by
    apply vertical_le_chord f b P W inside (by simpa using tn) _ mem
    rw [eq,derivative]
    exact ⟨polar t x,⟨x,rfl⟩,rfl⟩
  have even:k.1=0 := by
    by_contra odd
    have one:k.1=1:=((show ∀ s:F,s=0 ∨ s=1 from by decide) k.1).resolve_left odd
    let z:=f.symm k.2
    have same:k=delta f z := Prod.ext one (f.apply_symm_apply _).symm
    have sub : (univ:Finset (Cube n))⊆{z,z+t} := by
      intro x _
      have hits:=(delta_mem f f.injective x (x+t) z).mp (same ▸ common x)
      rcases hits with h|h
      · simp [h]
      · have rel:x=z+t := by rw [h,add_assoc,ZModModule.add_self,add_zero]
        simp [rel]
    have le:=(card_le_card sub).trans Finset.card_le_two
    simp [Cube] at le
    have := Nat.pow_le_pow_right (by decide : 0<2) large
    omega
  have sum (x:Cube n) := even_member f x (x+t) kn even (common x)
  exact ⟨t,tn,eq,fun x=>(sum x).symm.trans (by simpa using sum 0)⟩

def distinguished (n:ℕ) : Set (E n) := {z | z.1=0 ∧ z.2.1=1}
theorem distinguished_card (n:ℕ) : (distinguished n).toFinset.card=2^n := by
  have eq : (distinguished n).toFinset=univ.image (fun x:Cube n=>((0,1,x):E n)) := by
    ext z
    obtain ⟨a,c,x⟩:=z
    change ((a,c,x)∈(distinguished n).toFinset) ↔ _
    rw [Set.mem_toFinset]
    change (a=0 ∧ c=1) ↔ _
    simp [eq_comm]
  rw [eq,card_image_of_injective _ (fun _ _ h=>congrArg (fun p:E n=>p.2.2) h)]
  simp [Cube]

theorem zero_slice (f:Cube n→Cube n) (b:Cube n→V n) {v:V n}
    (h:((0,v):E n)∈labels f b+labels f b) : v=0 ∨ v.1=1 := by
  obtain ⟨p,hp,q,hq,e⟩:=mem_add.mp h
  obtain ⟨x,s,rfl⟩:=(mem_labels _ _ _).mp hp
  obtain ⟨y,t,rfl⟩:=(mem_labels _ _ _).mp hq
  have z:quad x+quad y=0 := congrArg Prod.fst e
  rw [←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at z
  have same:=quad_inj z
  subst y
  have val: b x+s • delta f x+(b x+t • delta f x)=v := congrArg Prod.snd e
  have val':(s+t) • delta f x=v := by rwa [add_add_add_comm,ZModModule.add_self,zero_add,←add_smul] at val
  rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) (s+t) with h|h <;> rw [h] at val'
  · left;simpa using val'.symm
  · right;rw [←val',one_smul];rfl

private theorem zero_omitted (large:3≤n) (f:Cube n ≃ Cube n) (b:Cube n→V n)
    (P:E n) (W:Submodule F (E n)) (dim:Module.finrank F W=n)
    (inside:P +ᵥ (W:Set (E n))⊆↑(labels f b+labels f b)) :
    (0:E n)∉P +ᵥ (W:Set (E n)) := by
  rintro ⟨w,hw,e⟩
  change P+w=0 at e
  rw [←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at e
  have memP:P∈W:=e.symm ▸ hw
  have le:Module.finrank F (Cube 3)≤Module.finrank F W := by simpa [Cube,dim] using large
  obtain ⟨j,inj⟩:=finrank_le_iff_exists_linearMap.mp le
  let g:=W.subtype.comp j
  have gi:Function.Injective g:=Subtype.val_injective.comp inj
  apply avoids_linear f f.injective b
  refine ⟨g.range,?_,?_⟩
  · rw [g.finrank_range_of_inj gi];simp [Cube]
  · rintro _ ⟨v,rfl⟩
    apply inside
    refine ⟨P+g v,W.add_mem memP (j v).property,?_⟩
    change P+(P+g v)=g v
    rw [←add_assoc,ZModModule.add_self,zero_add]

/-- An additional top-dimensional affine flat requires a constant nonzero derivative direction. -/
theorem top_flat_alternative (large:4≤n) (f:Cube n ≃ Cube n) (b:Cube n→V n)
    (P:E n) (W:Submodule F (E n)) (dim:Module.finrank F W=n)
    (inside:P +ᵥ (W:Set (E n))⊆↑(labels f b+labels f b)) :
    P +ᵥ (W:Set (E n))=distinguished n ∨
    ∃ t:Cube n,t≠0 ∧ baseFlat P W=fiber t ∧ ∀ x:Cube n,f x+f (x+t)=f 0+f t := by
  by_cases nonzero:∃ z∈baseFlat P W,z≠0
  · exact Or.inr (constant_derivative large f b P W dim inside nonzero)
  push Not at nonzero
  left
  apply Set.toFinset_inj.mp
  apply eq_of_subset_of_card_le
  · apply Set.toFinset_subset_toFinset.mpr
    intro z hz
    have first:=nonzero z.1 ((mem_baseFlat P W _).mpr ⟨z.2,hz⟩)
    obtain ⟨z,v⟩:=z
    change z=0 at first
    subst z
    refine ⟨rfl,?_⟩
    rcases zero_slice f b (inside hz) with h|h
    · subst v
      exact False.elim (zero_omitted (by omega) f b P W dim inside hz)
    · exact h
  · rw [distinguished_card,flat_card,dim]

/-- A constant derivative produces a second top-dimensional flat when all lower labels have zero vertical coordinate. -/
theorem flat_of_derivative (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0)
    (constant:∀ x:Cube n, f x+f (x+t)=f 0+f t) :
    ∃ (P:E n) (W:Submodule F (E n)),Module.finrank F W=n ∧
      P +ᵥ (W:Set (E n))⊆↑(labels f 0+labels f 0) ∧ P +ᵥ (W:Set (E n))≠distinguished n := by
  let k:V n := (0,f 0+f t)
  have kn:k≠0 := by
    intro h
    have h':f 0+f t=0:=congrArg Prod.snd h
    rw [←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at h'
    exact tn (f.injective h').symm
  let W:=((polar t).range.prod (F ∙ k))
  let P:E n := (quad 0+quad t,0)
  refine ⟨P,W,?_,?_,?_⟩
  · let j : ((polar t).range × ↥(F ∙ k)) ≃ₗ[F] W :=
      { toFun := fun v=>⟨(v.1.val,v.2.val),v.1.property,v.2.property⟩
        invFun := fun v=>(⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl
        map_add' := fun _ _=>rfl
        map_smul' := fun _ _=>rfl }
    rw [←j.finrank_eq,Module.finrank_prod,finrank_span_singleton kn]
    exact fiber_dimension tn
  · rintro _ ⟨⟨z,v⟩,⟨⟨x,rfl⟩,hv⟩,rfl⟩
    obtain ⟨s,rfl⟩:=Submodule.mem_span_singleton.mp hv
    change (quad 0+quad t+polar t x,0+s • k)∈labels f 0+labels f 0
    rw [zero_add,←derivative]
    apply (chord_slice f 0 (show x≠x+t by simpa using tn) _).mpr
    refine ⟨s,s,?_⟩
    change s • k=(0+s • delta f x)+(0+s • delta f (x+t))
    rw [zero_add,zero_add,←smul_add]
    congr 1
    exact Prod.ext (ZModModule.add_self _).symm (constant x).symm
  · intro same
    have mem:P∈P +ᵥ (W:Set (E n)):=⟨0,W.zero_mem,add_zero _⟩
    have bad:=same ▸ mem
    exact zero_ne_one (show (0:F)=1 from bad.2)

/-- A zero-offset configuration has a unique top flat exactly when its permutation has no nonzero constant derivative direction. -/
theorem unique_top_iff (large:4≤n) (f:Cube n ≃ Cube n) :
    (∀ (P:E n) (W:Submodule F (E n)), Module.finrank F W=n →
      P +ᵥ (W:Set (E n))⊆↑(labels f 0+labels f 0) → P +ᵥ (W:Set (E n))=distinguished n) ↔
    ¬ ∃ t:Cube n,t≠0 ∧ ∀x:Cube n,f x+f (x+t)=f 0+f t := by
  constructor
  · rintro uniq ⟨t,tn,constant⟩
    obtain ⟨P,W,r,h,ne⟩:=flat_of_derivative f tn constant
    exact ne (uniq P W r h)
  · intro absent P W r h
    rcases top_flat_alternative large f 0 P W r h with eq|⟨t,tn,_,constant⟩
    · exact eq
    · exact False.elim (absent ⟨t,tn,constant⟩)

end Green51PermutedPairs

#print axioms Green51PermutedPairs.constant_derivative
#print axioms Green51PermutedPairs.top_flat_alternative
#print axioms Green51PermutedPairs.flat_of_derivative
#print axioms Green51PermutedPairs.unique_top_iff
