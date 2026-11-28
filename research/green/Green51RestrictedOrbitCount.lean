import Green51TranslationClasses

/-! # Translation classes meeting a family in a uniform number of shifts -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def periods (S : Finset G) : Finset G := univ.filter fun b => translate S b=S

private theorem translated_periods (S : Finset G) (a : G) : periods (translate S a)=periods S := by
  classical
  ext b
  simp only [periods,mem_filter,mem_univ,true_and]
  rw [translate_twice]
  constructor
  · intro eq
    have e := congrArg (fun T => translate T (-a)) eq
    simpa only [translate_twice,add_right_comm a b (-a),add_neg_cancel,zero_add,translate_zero] using e
  · intro eq
    rw [add_comm,←translate_twice,eq]

private theorem translates_to (S : Finset G) (a : G) :
    (univ.filter fun b => translate S b=translate S a).card=(periods S).card := by
  classical
  have eq : (univ.filter fun b => translate S b=translate S a)=translate (periods S) a := by
    ext b
    constructor
    · intro hb
      have e := congrArg (fun T => translate T (-a)) (mem_filter.mp hb).2
      apply mem_map.mpr
      refine ⟨b-a,mem_filter.mpr ⟨mem_univ _,?_⟩,by change b-a+a=b; abel⟩
      simpa only [translate_twice,add_neg_cancel,translate_zero,sub_eq_add_neg] using e
    · intro hb
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hb
      exact mem_filter.mpr ⟨mem_univ _,by
        change translate S (x+a)=translate S a
        rw [←translate_twice,(mem_filter.mp hx).2]⟩
  rw [eq,translate_card]

private theorem same_periods {S T : Finset G} (eq : translationClass T=translationClass S) :
    periods T=periods S := by
  obtain ⟨a,rfl⟩ := (same_class_iff _ _).mp eq
  exact translated_periods S a

/-- The number of representatives times the stabilizer order is the number of allowed shifts. -/
theorem restricted_fiber_size (family : Finset (Finset G)) (S : Finset G) :
    (family.filter fun T => translationClass T=translationClass S).card*(periods S).card =
      (univ.filter fun b => translate S b∈family).card := by
  classical
  let V := univ.filter fun b => translate S b∈family
  let U := family.filter fun T => translationClass T=translationClass S
  have image : V.image (translate S)=U := by
    ext T
    constructor
    · intro h
      obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp hb).2,(same_class_iff _ _).mpr ⟨_,rfl⟩⟩
    · intro h
      obtain ⟨inF,eq⟩ := mem_filter.mp h
      obtain ⟨b,rfl⟩ := (same_class_iff _ _).mp eq
      exact mem_image.mpr ⟨b,mem_filter.mpr ⟨mem_univ _,inF⟩,rfl⟩
  have count := card_eq_sum_card_image (translate S) V
  rw [image] at count
  have val (T : Finset G) (ht : T∈U) :
      (V.filter (fun b => translate S b=T)).card=(periods T).card := by
    obtain ⟨inF,eq⟩ := mem_filter.mp ht
    obtain ⟨a,rfl⟩ := (same_class_iff _ _).mp eq
    rw [translated_periods,←translates_to S a]
    congr 1
    ext b
    simp only [V,mem_filter,mem_univ,true_and]
    exact and_iff_right_of_imp (fun e => e ▸ inF)
  have const (T : Finset G) (hT : T∈U) : (periods T).card=(periods S).card :=
    congrArg Finset.card (same_periods (mem_filter.mp hT).2)
  rw [sum_congr rfl val,sum_congr rfl const,sum_const,smul_eq_mul] at count
  exact count.symm

/-- When each member has exactly `m` admissible shifts, the restricted class count
satisfies the fixed-point sum, even when the family is not closed under translation. -/
theorem restricted_orbit_count (family : Finset (Finset G)) (m : ℕ)
    (allowed : ∀ S ∈ family, (univ.filter fun b => translate S b∈family).card=m) :
    (family.image translationClass).card*m=∑ t : G, (family.filter fun S => translate S t=S).card := by
  classical
  have group_sum (S : Finset G) (hS : S∈family) :
      (∑ T ∈ family.filter (fun T => translationClass T=translationClass S), (periods T).card)=m := by
    rw [sum_congr rfl (fun T hT => congrArg Finset.card (same_periods (mem_filter.mp hT).2)),
      sum_const,smul_eq_mul]
    exact (restricted_fiber_size family S).trans (allowed S hS)
  have each (U) (hU : U∈family.image translationClass) :
      (∑ T ∈ family.filter (fun T => translationClass T=U), (periods T).card)=m := by
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hU
    exact group_sum S hS
  have count : (family.image translationClass).card*m=∑ S ∈ family, (periods S).card := by
    calc
      _ = ∑ _ ∈ family.image translationClass, m := by rw [sum_const,smul_eq_mul]
      _ = _ := by
        rw [←sum_congr rfl each]
        exact sum_fiberwise_of_maps_to (fun S h => mem_image_of_mem translationClass h) _
  rw [count]
  simp only [periods,card_filter]
  rw [sum_comm]

end Green51OriginRecovery
#print axioms Green51OriginRecovery.restricted_fiber_size
#print axioms Green51OriginRecovery.restricted_orbit_count
