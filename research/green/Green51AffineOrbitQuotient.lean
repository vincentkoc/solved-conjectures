import Green51AffineRankCounts
import Green51FixedKernelCount

/-! # Translation-invariant families of complements of affinely nonspanning sets -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold Green51AffineEnumeration Green51OriginRecovery Green51PeriodQuotients
open scoped Classical
variable {G H : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [Fintype H] [DecidableEq H]

/-- Some translate of the missing set lies in a level-one linear slice. -/
def admitsOrigin (D : Finset G) : Prop := ∃ b, separated (Green51OriginRecovery.translate D b)

omit [Fintype G] [DecidableEq G] in
theorem admits_translate (D : Finset G) (a : G) :
    admitsOrigin (Green51OriginRecovery.translate D a) ↔ admitsOrigin D := by
  unfold admitsOrigin
  simp only [translate_twice]
  constructor
  · rintro ⟨b,h⟩; exact ⟨a+b,h⟩
  · rintro ⟨b,h⟩; exact ⟨b-a,by simpa only [add_sub_cancel] using h⟩

/-- All translates are included, even when a particular origin lies in the missing affine span. -/
noncomputable def properOutputs (G : Type*) [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (k : ℕ) : Finset (Finset G) := univ.filter fun S => Sᶜ.card=k ∧ admitsOrigin Sᶜ

theorem proper_translate (S : Finset G) (b : G) (k : ℕ) :
    Green51OriginRecovery.translate S b∈properOutputs G k ↔ S∈properOutputs G k := by
  simp only [properOutputs,mem_filter,mem_univ,true_and,translate_compl,translate_card,admits_translate]

omit [DecidableEq G] [Fintype H] in
private theorem translated_pull (f : G →ₗ[F] H) (T : Finset H) (b : G) :
    Green51OriginRecovery.translate (pull f T) b=pull f (Green51OriginRecovery.translate T (f b)) := by
  classical
  ext x
  obtain ⟨y,rfl⟩ := (Equiv.addRight b).surjective x
  have forward : f ((Equiv.addRight b) y)=(Equiv.addRight (f b)) (f y) := f.map_add y b
  simp only [Green51OriginRecovery.translate,mem_map_equiv,mem_pull,Equiv.symm_apply_apply,forward]

omit [DecidableEq G] [Fintype H] in
private theorem separated_pull (f : G →ₗ[F] H) (onto : Function.Surjective f) (T : Finset H) :
    separated (pull f T) ↔ separated T := by
  obtain ⟨j,hj⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr onto)
  have sec (y) : f (j y)=y := LinearMap.congr_fun hj y
  constructor
  · rintro ⟨g,ones⟩
    exact ⟨g.comp j,fun y hy => ones _ ((mem_pull _ _ _).mpr ((sec y).symm ▸ hy))⟩
  · rintro ⟨g,ones⟩
    exact ⟨g.comp f,fun x hx => ones _ ((mem_pull _ _ _).mp hx)⟩

omit [DecidableEq G] [Fintype H] in
theorem admits_pull (f : G →ₗ[F] H) (onto : Function.Surjective f) (T : Finset H) :
    admitsOrigin (pull f T) ↔ admitsOrigin T := by
  unfold admitsOrigin
  simp only [translated_pull,separated_pull f onto]
  constructor
  · rintro ⟨b,h⟩; exact ⟨f b,h⟩
  · rintro ⟨y,h⟩; obtain ⟨b,rfl⟩ := onto y; exact ⟨b,h⟩

private theorem proper_pull (f : G →ₗ[F] H) (onto : Function.Surjective f)
    (T : Finset H) (k : ℕ) :
    pull f T∈properOutputs G ((f.ker : Set G).toFinset.card*k) ↔ T∈properOutputs H k := by
  have pos : 0<(f.ker : Set G).toFinset.card := card_pos.mpr ⟨0,Set.mem_toFinset.mpr f.ker.zero_mem⟩
  simp only [properOutputs,mem_filter,mem_univ,true_and,pull_compl,admits_pull f onto,
    card_pull f onto,Nat.mul_right_inj pos.ne']

theorem proper_fixed_kernel (f : G →ₗ[F] H) (onto : Function.Surjective f) (k : ℕ) :
    ((properOutputs G ((f.ker : Set G).toFinset.card*k)).filter
      (fun S => ∀ t∈f.ker, Green51OriginRecovery.translate S t=S)).card = (properOutputs H k).card := by
  classical
  symm
  apply card_bij (fun T _ => pull f T)
  · intro T hT; exact mem_filter.mpr ⟨(proper_pull f onto T k).mpr hT,pull_fixed f T⟩
  · intro T _ U _ eq; simpa only [image_pull f onto] using congrArg (fun S : Finset G => S.image f) eq
  · intro S hS
    obtain ⟨h,stable⟩ := mem_filter.mp hS
    have eq := saturated f S stable
    exact ⟨_,(proper_pull f onto (S.image f) k).mp (eq.symm ▸ h),eq⟩

end Green51AffineTranslation
#print axioms Green51AffineTranslation.admits_translate
#print axioms Green51AffineTranslation.proper_translate
#print axioms Green51AffineTranslation.admits_pull
#print axioms Green51AffineTranslation.proper_fixed_kernel
