import Green51RootedAffineSets
import Green51TranslationClasses

/-! # Affine hyperplanes reached by translating a missing set -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold Green51AffineEnumeration Green51OriginRecovery
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
private theorem shifted_eq_translate (D : Finset G) (b : G) :
    shifted D b=Green51OriginRecovery.translate D b := rfl

omit [Fintype G] [DecidableEq G] in
/-- Moving an arbitrary anchor to zero gives an exact test for each origin. -/
theorem separated_translate {D : Finset G} {a : G} (ha : a∈D) (b : G) :
    separated (Green51OriginRecovery.translate D b) ↔
      a+b∉Submodule.span F ((Green51OriginRecovery.translate D a : Finset G) : Set G) := by
  have hz : 0∈Green51OriginRecovery.translate D a :=
    mem_map.mpr ⟨a,ha,ZModModule.add_self a⟩
  have eq := separated_shifted_iff (Green51OriginRecovery.translate D a) hz (a+b)
  simpa only [shifted_eq_translate,translate_twice,←add_assoc,ZModModule.add_self,zero_add] using eq

/-- A missing set with a fixed anchor has one separating origin for each point outside its
affine span. -/
theorem separated_origins {D : Finset G} {a : G} (ha : a∈D) :
    (univ.filter fun b => separated (Green51OriginRecovery.translate D b)).card =
      Fintype.card G-2^Module.finrank F (Submodule.span F ((Green51OriginRecovery.translate D a : Finset G) : Set G)) := by
  classical
  let W := Submodule.span F ((Green51OriginRecovery.translate D a : Finset G) : Set G)
  have eq : (univ.filter fun b => separated (Green51OriginRecovery.translate D b)) =
      shifted (W : Set G).toFinsetᶜ a := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_shifted,mem_compl,Set.mem_toFinset,
      SetLike.mem_coe,separated_translate ha]
    rw [add_comm a x]
  rw [eq,shifted_eq_translate,translate_card,card_compl,Set.toFinset_card]
  change Fintype.card G-Fintype.card W=_
  rw [Module.card_eq_pow_finrank (K := F) (V := W),ZMod.card]

omit [Fintype G] [DecidableEq G] in
theorem direction_at_anchor {D : Finset G} {a : G} (ha : a∈D) :
    (affineSpan F (D : Set G)).direction=Submodule.span F ((Green51OriginRecovery.translate D a : Finset G) : Set G) := by
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right F (show a∈(D : Set G) from ha)]
  apply congrArg (Submodule.span F)
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact mem_map.mpr ⟨x,hx,by change x+a=x-a;rw [sub_eq_add_neg,ZModModule.neg_eq_self]⟩
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    exact ⟨x,hx,by change x-a=x+a; rw [sub_eq_add_neg,ZModModule.neg_eq_self]⟩

omit [Fintype G] [DecidableEq G] in
/-- A translate fits in a level-one hyperplane exactly when its shift is outside the affine span. -/
theorem separating_origin_iff {D : Finset G} (live : D.Nonempty) (b : G) :
    separated (Green51OriginRecovery.translate D b) ↔ b∉affineSpan F (D : Set G) := by
  obtain ⟨a,ha⟩ := live
  rw [separated_translate ha,←direction_at_anchor ha]
  have iff := AffineSubspace.vsub_right_mem_direction_iff_mem
    (mem_affineSpan F (show a∈(D : Set G) from ha)) b
  simpa only [vsub_eq_sub,sub_eq_add_neg,ZModModule.neg_eq_self,add_comm b a] using not_congr iff

end Green51AffineTranslation
#print axioms Green51AffineTranslation.separated_translate
#print axioms Green51AffineTranslation.separated_origins
#print axioms Green51AffineTranslation.direction_at_anchor
#print axioms Green51AffineTranslation.separating_origin_iff
