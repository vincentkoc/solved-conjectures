import Green51TranslationClasses

/-! # Translation types of subsets of a four-point binary fibre -/

namespace Green51FrameIsomorphisms
open Finset Green51OriginRecovery
abbrev Four := ZMod 2 × ZMod 2

/-- Cardinality and the direction of a two-point set distinguish all translation classes
in a binary plane. -/
theorem four_fibre_types : ∀ S T : Finset Four,
    (∃ b : Four, Green51OriginRecovery.translate S b=T) ↔
      S.card=T.card ∧ (S.card=2 → (∑ x∈S,x)=∑ y∈T,y) := by
  decide +kernel

private theorem additive_test : ∀ f : Four → Four, f 0=0 → Function.Injective f →
    ∀ x y, f (x+y)=f x+f y := by decide +kernel

/-- Every permutation of the three nonzero directions arises from a binary linear change
of coordinates. -/
def linearize (e : Equiv.Perm Four) (fixes : e 0=0) : Four ≃ₗ[ZMod 2] Four where
  toEquiv := e
  map_add' := additive_test e fixes e.injective
  map_smul' a x := by
    have scalars : ∀ c : ZMod 2, c=0 ∨ c=1 := by decide
    rcases scalars a with rfl | rfl <;> simp [fixes]

theorem moved_fibre_types (S T : Finset Four) (u : Four ≃ₗ[ZMod 2] Four) :
    (∃ b : Four, S.image (fun p => u p+b)=T) ↔
      S.card=T.card ∧ (S.card=2 → u (∑ x∈S,x)=∑ y∈T,y) := by
  classical
  let U := S.image u
  have sz : U.card=S.card := card_image_of_injective _ u.injective
  have total : (∑ x∈U,x)=u (∑ p∈S,p) := by
    dsimp [U];rw [sum_image (fun _ _ _ _ h => u.injective h),map_sum]
  have eq (b : Four) : Green51OriginRecovery.translate U b=S.image (fun p => u p+b) := by
    ext x
    simp only [Green51OriginRecovery.translate,mem_map,mem_image,U]
    constructor
    · rintro ⟨y,⟨p,hp,rfl⟩,rfl⟩; exact ⟨p,hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩; exact ⟨u p,⟨p,hp,rfl⟩,rfl⟩
  simpa only [eq,sz,total] using four_fibre_types U T

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.four_fibre_types
#print axioms Green51FrameIsomorphisms.linearize
#print axioms Green51FrameIsomorphisms.moved_fibre_types
