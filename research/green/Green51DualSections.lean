import Green51ShortenedColumns
import Green51ShortenedProfiles

/-! # A level of an affine functional from a word of the augmented dual -/

open Finset Green50Downsets Green50Sharp Green51ShortenedColumns Green51WeightTransform
open scoped Classical
namespace Green51DualSections
local notation "F" => ZMod 2
local notation "V" => Cube 11

theorem descend {n : ℕ} (P : Cube n →ₗ[F] F×V) (onto : Function.Surjective P)
    {z : Cube n} (hz : z∈dualWords P.ker) :
    ∃ l : Module.Dual F (F×V), ∀ i,l (P (Pi.single i 1))=z i := by
  classical
  obtain ⟨J,sec⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr onto)
  let f := Fintype.linearCombination F z
  have ev (w : Cube n) : f w=dotProduct z w := by
    simp [f,Fintype.linearCombination_apply,dotProduct,mul_comm]
  have pull (w : Cube n) : f (J (P w))=f w := by
    have k : J (P w)-w∈P.ker := by
      change P (J (P w)-w)=0
      rw [map_sub,show P (J (P w))=P w from LinearMap.congr_fun sec _,sub_self]
    have h := (mem_filter.mp hz).2 (⟨_,k⟩ : P.ker)
    change dotProduct z (J (P w)-w)=0 at h
    rw [←ev,map_sub] at h
    exact sub_eq_zero.mp h
  exact ⟨f.comp J,fun i => (pull _).trans (by simp [f,Fintype.linearCombination_apply_single])⟩


theorem level {A : Finset V} (P : Cube A.card →ₗ[F] F×V) (onto : Function.Surjective P)
    (unit : ∀i : Fin A.card, P (Pi.single i 1)=(1,(A.equivFin.symm i).val))
    {z : Cube A.card} (dual : z∈dualWords P.ker) (pos : 0<(supp z).card)
    (small : (supp z).card<A.card) :
    ∃ (L:V →ₗ[F] F) (c:F), L≠0 ∧ (A.filter (fun x => L x=c)).card=A.card-(supp z).card := by
  classical
  obtain ⟨l,hl⟩ := descend P onto dual
  let idx (i : Fin A.card) := (A.equivFin.symm i).val
  let L := l.comp (LinearMap.inr F F V)
  let c := -l (1,0)
  have test (i : Fin A.card) : L (idx i)=c ↔ z i=0 := by
    have split : ((1:F),idx i) = (1,0)+(0,idx i) := by simp
    have eq := hl i
    rw [unit] at eq
    change l (1,idx i)=z i at eq
    rw [split,map_add] at eq
    change L (idx i)= -l (1,0) ↔ z i=0
    change l (1,0)+L (idx i)=z i at eq
    rw [←eq,add_comm,add_eq_zero_iff_eq_neg]
  have cut : A.filter (fun x => L x=c)=(supp z)ᶜ.image idx := by
    ext x
    constructor
    · intro hx
      obtain ⟨xA,zero⟩ := mem_filter.mp hx
      let i := A.equivFin ⟨x,xA⟩
      have eq : idx i=x := congrArg Subtype.val (A.equivFin.symm_apply_apply _)
      exact mem_image.mpr ⟨i,mem_compl.mpr (by simpa [supp] using (test i).mp (eq ▸ zero)),eq⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨(A.equivFin.symm i).property,(test i).mpr (by
        simpa [supp] using mem_compl.mp hi)⟩
  have card : (A.filter (fun x => L x=c)).card=A.card-(supp z).card := by
    have inj : Function.Injective idx := Subtype.val_injective.comp A.equivFin.symm.injective
    rw [cut,card_image_of_injective _ inj,
      card_compl,Fintype.card_fin]
  refine ⟨L,c,?_,card⟩
  intro zero
  by_cases k:c=0
  · simp [zero,k] at card; omega
  · simp [zero,Ne.symm k] at card; omega

end Green51DualSections
#print axioms Green51DualSections.descend
#print axioms Green51DualSections.level
