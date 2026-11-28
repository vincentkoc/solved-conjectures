import Green51QuadraticFlats

/-! # Two labels at each point of the binary quadratic graph -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise symmDiff
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

abbrev V (n:ℕ) := F × Cube n
abbrev E (n:ℕ) := Target n × V n

def delta (f:Cube n→Cube n) (x:Cube n) : V n := (1,f x)
def lower (b:Cube n→V n) (x:Cube n) : E n := (quad x,b x)
def upper (f:Cube n→Cube n) (b:Cube n→V n) (x:Cube n) : E n := (quad x,b x+delta f x)
def labels (f:Cube n→Cube n) (b:Cube n→V n) : Finset (E n) :=
  univ.image (lower b) ∪ univ.image (upper f b)

theorem short_projection (U W:Finset (Cube n)) (small:U.card+W.card≤6)
    (eq:(∑ x∈U,quad x)+(∑ x∈W,quad x)=0) : U=W := by
  have h₁ := sum_inter_add_sum_sdiff U W (@quad n)
  have h₂ := sum_inter_add_sum_sdiff W U (@quad n)
  rw [inter_comm W U] at h₂
  have dis : Disjoint (U \ W) (W \ U) := by
    rw [disjoint_left];intro x hx h
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp h).1
  have total : ∑ x∈(U ∆ W),quad x=0 := by
    rw [←eq,Finset.symmDiff_def,sum_union dis,←h₁,←h₂,add_add_add_comm,ZModModule.add_self,zero_add]
  by_contra h
  have ne : (U ∆ W).Nonempty := by simpa using h
  have size : (U ∆ W).card≤6 := by
    rw [Finset.symmDiff_def,card_union_of_disjoint dis]
    exact (Nat.add_le_add (card_le_card sdiff_subset) (card_le_card sdiff_subset)).trans small
  have R := relation_size _ ne total
  have pos := card_pos.mpr ne
  generalize (U ∆ W).card=k at R pos size
  interval_cases k <;> norm_num at R

theorem delta_relation (f:Cube n→Cube n) (inj:Function.Injective f) (U:Finset (Cube n))
    (size:U.card=2 ∨ U.card=3) (total:∑ x∈U,delta f x=0) : False := by
  have parity := congrArg Prod.fst total
  simp only [Prod.fst_sum,delta,sum_const,nsmul_eq_mul,mul_one,Prod.fst_zero] at parity
  rcases size with h|h
  · obtain ⟨x,y,xy,rfl⟩ := card_eq_two.mp h
    simp only [sum_insert (by simpa using xy : x∉({y}:Finset _)),sum_singleton] at total
    have eq := congrArg Prod.snd total
    change f x + f y = 0 at eq
    rw [←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at eq
    exact xy (inj eq)
  · rw [h] at parity
    exact (by decide : (3:F)≠0) parity

private theorem lower_inj (b:Cube n→V n) : Function.Injective (lower b) :=
  fun _ _ h => quad_inj (congrArg Prod.fst h)
private theorem upper_inj (f:Cube n→Cube n) (b:Cube n→V n) : Function.Injective (upper f b) :=
  fun _ _ h => quad_inj (congrArg Prod.fst h)
private theorem disjoint_rows (f:Cube n→Cube n) (b:Cube n→V n) (U W:Finset (Cube n)) :
    Disjoint (U.image (lower b)) (W.image (upper f b)) := by
  apply disjoint_left.mpr
  rintro _ hu hw
  obtain ⟨x,_,rfl⟩ := mem_image.mp hu
  obtain ⟨y,_,eq⟩ := mem_image.mp hw
  have same : y=x := quad_inj (congrArg Prod.fst eq)
  subst y
  have h := congrArg Prod.snd eq
  change b x+delta f x=b x at h
  exact one_ne_zero (congrArg Prod.fst (add_eq_left.mp h))

theorem labels_card (f:Cube n→Cube n) (b:Cube n→V n) :
    (labels f b).card=2^(n+1) := by
  rw [labels,card_union_of_disjoint (disjoint_rows _ _ _ _),
    card_image_of_injective _ (lower_inj _),card_image_of_injective _ (upper_inj _ _)]
  simp [Cube,pow_succ,Nat.mul_two]

private theorem split_relation (f:Cube n→Cube n) (b:Cube n→V n)
    (T:Finset (E n)) (inside:T⊆labels f b) :
    ∃ U W:Finset (Cube n),T=U.image (lower b) ∪ W.image (upper f b) := by
  refine ⟨univ.filter (fun x => lower b x∈T),univ.filter (fun x => upper f b x∈T),?_⟩
  ext y
  constructor
  · intro hy
    rcases mem_union.mp (inside hy) with l|r
    · obtain ⟨x,_,rfl⟩ := mem_image.mp l
      exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hy⟩))
    · obtain ⟨x,_,rfl⟩ := mem_image.mp r
      exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hy⟩))
  · intro h
    rcases mem_union.mp h with h|h <;> obtain ⟨x,hx,rfl⟩ := mem_image.mp h <;>
      exact (mem_filter.mp hx).2

theorem avoids_linear (f:Cube n→Cube n) (inj:Function.Injective f) (b:Cube n→V n) :
    ¬∃ W:Submodule F (E n), Module.finrank F W=3 ∧ ∀ w∈W,w∈labels f b+labels f b := by
  rintro ⟨W,dim,ins⟩
  have free (T:Finset (E n)) (sub:T⊆labels f b) (sz:T.card=4 ∨ T.card=6)
      (zero:∑ z∈T,z=0) : False := by
    obtain ⟨U,V',rfl⟩ := split_relation f b T sub
    rw [card_union_of_disjoint (disjoint_rows _ _ _ _),card_image_of_injective _ (lower_inj _),
      card_image_of_injective _ (upper_inj _ _)] at sz
    rw [sum_union (disjoint_rows _ _ _ _),sum_image (lower_inj _).injOn,
      sum_image (upper_inj _ _).injOn] at zero
    have fst := congrArg Prod.fst zero
    simp only [Prod.fst_add,Prod.fst_sum,lower,upper,Prod.fst_zero] at fst
    have same := short_projection U V' (by omega) fst
    subst V'
    have snd := congrArg Prod.snd zero
    simp only [Prod.snd_add,Prod.snd_sum,lower,upper,Prod.snd_zero,sum_add_distrib,
      ←add_assoc,ZModModule.add_self,zero_add] at snd
    exact delta_relation f inj U (by omega) snd
  have r := Green51SparseDimensions.rank_without_relation (labels f b) free W ins
  omega

theorem vertical_flat (f:Cube n ≃ Cube n) (b:Cube n→V n) :
    ∃ (W:Submodule F (E n)) (p:E n), Module.finrank F W=n ∧ p +ᵥ (W:Set (E n)) ⊆ ↑(labels f b+labels f b) := by
  let L := (LinearMap.inr F (Target n) (V n)).comp (LinearMap.inr F F (Cube n))
  have inj : Function.Injective L := LinearMap.inr_injective.comp LinearMap.inr_injective
  refine ⟨L.range,(0,1,0),?_,?_⟩
  · rw [L.finrank_range_of_inj inj];simp [Cube]
  · rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    let x := f.symm v
    have e : (0,1,0)+L v=lower b x+upper f b x := by
      apply Prod.ext
      · change (0+0:Target n)=quad x+quad x
        rw [zero_add,ZModModule.add_self]
      · change ((1,0):V n)+(0,v) = b x+(b x+delta f x)
        rw [←add_assoc,ZModModule.add_self,zero_add]
        apply Prod.ext
        · change (1:F)+0=1;simp
        · change 0+v=f (f.symm v);simp
    change ((0,1,0):E n)+L v ∈ labels f b+labels f b
    rw [e]
    exact add_mem_add (mem_union_left _ (mem_image_of_mem _ (mem_univ _)))
      (mem_union_right _ (mem_image_of_mem _ (mem_univ _)))

theorem chord_unique {x y z w:Cube n} (ne:x≠y) (eq:quad x+quad y=quad z+quad w) :
    (x=z ∧ y=w) ∨ (x=w ∧ y=z) := by
  have other : z≠w := by
    rintro rfl
    rw [ZModModule.add_self,←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at eq
    exact ne (quad_inj eq)
  have zero : (∑ a∈({x,y}:Finset _),quad a)+(∑ a∈({z,w}:Finset _),quad a)=0 := by
    simp only [sum_insert (by simpa using ne : x∉({y}:Finset _)),
      sum_insert (by simpa using other : z∉({w}:Finset _)),sum_singleton,eq,ZModModule.add_self]
  have same := short_projection {x,y} {z,w} (by simp [ne,other]) zero
  have xmem : x=z ∨ x=w := by simpa using (same ▸ mem_insert_self x {y} : x∈({z,w}:Finset _))
  have ymem : y=z ∨ y=w := by simpa using (same ▸ (show y∈({x,y}:Finset _) by simp) : y∈({z,w}:Finset _))
  grind

end Green51PermutedPairs

#print axioms Green51PermutedPairs.labels_card
#print axioms Green51PermutedPairs.avoids_linear
#print axioms Green51PermutedPairs.vertical_flat
#print axioms Green51PermutedPairs.chord_unique
