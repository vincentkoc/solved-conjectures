import Green51CircuitOverlap

/-! # Translation classes of finite sets in a binary vector space -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold
open scoped Classical
variable {G : Type*} [AddCommGroup G]

def translate (S : Finset G) (b : G) : Finset G := S.map (Equiv.addRight b).toEmbedding

@[simp] theorem translate_card (S : Finset G) (b : G) : (translate S b).card=S.card :=
  card_map _

@[simp] theorem translate_zero (S : Finset G) : translate S 0=S := by
  classical
  ext x
  simp only [translate,Finset.mem_map_equiv]
  rw [show (Equiv.addRight (0:G)).symm x = x from
    (Equiv.symm_apply_eq _).mpr (add_zero x).symm]

theorem translate_twice (S : Finset G) (a b : G) :
    translate (translate S a) b=translate S (a+b) := by
  classical
  unfold translate
  rw [map_map]
  congr 1
  ext x
  exact add_assoc x a b

theorem translate_compl [Fintype G] [DecidableEq G] (S : Finset G) (b : G) :
    (translate S b)ᶜ=translate Sᶜ b := by
  ext x
  simp [translate,Finset.mem_map_equiv]

theorem odd_translation_injective [Module F G] (S : Finset G) (odd : Odd S.card) :
    Function.Injective (translate S) := by
  have total (b : G) : (∑ x ∈ translate S b, x)=(∑ x ∈ S, x)+b := by
    unfold translate
    rw [sum_map]
    change (∑ x ∈ S, (x+b))=_
    rw [sum_add_distrib,sum_const]
    obtain ⟨j,hj⟩ := odd
    rw [hj,add_nsmul,one_nsmul,show 2*j=j*2 by omega,mul_nsmul,two_nsmul,ZModModule.add_self,zero_add]
  intro a b eq
  exact add_left_cancel ((total a).symm.trans ((congrArg (fun T : Finset G => ∑ x ∈ T, x) eq).trans (total b)))

/-- All translates in the ambient group, including those outside a prescribed family. -/
noncomputable def translationClass [Fintype G] [DecidableEq G] (S : Finset G) : Finset (Finset G) :=
  univ.image (translate S)

theorem same_class_iff [Fintype G] [DecidableEq G] (S T : Finset G) :
    translationClass T=translationClass S ↔ ∃ b, translate S b=T := by
  classical
  constructor
  · intro eq
    have h : T ∈ translationClass T := mem_image.mpr ⟨0,mem_univ _,translate_zero T⟩
    obtain ⟨b,_,hb⟩ := mem_image.mp (eq ▸ h : T∈translationClass S)
    exact ⟨b,hb⟩
  · rintro ⟨b,rfl⟩
    ext V
    constructor
    · intro h
      obtain ⟨c,_,rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨b+c,mem_univ _,(translate_twice S b c).symm⟩
    · intro h
      obtain ⟨c,_,rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨c-b,mem_univ _,by rw [translate_twice]; simp⟩

/-- Count a family by the translation classes it meets when every nonempty intersection
with an ambient translation class has the same size. -/
theorem uniform_class_count [Fintype G] [DecidableEq G] (family : Finset (Finset G)) (m : ℕ)
    (fiber : ∀ S ∈ family, (family.filter (fun T => translationClass T=translationClass S)).card=m) :
    (family.image translationClass).card*m=family.card := by
  classical
  rw [card_eq_sum_card_image translationClass family]
  have value (U) (hu : U∈family.image translationClass) :
      (family.filter (fun T => translationClass T=U)).card=m := by
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hu
    exact fiber S hS
  rw [sum_congr rfl value,sum_const,smul_eq_mul]

end Green51OriginRecovery
#print axioms Green51OriginRecovery.odd_translation_injective
#print axioms Green51OriginRecovery.same_class_iff
#print axioms Green51OriginRecovery.uniform_class_count
