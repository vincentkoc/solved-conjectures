import Green51ShortenedColumns
import Green51ShortenedProfiles
import Green51ElevenRelations
import Green51FlatSections

/-! # A fifteen-point hyperplane section of every affine-flat avoiding eighteen-set -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51ShortenedColumns Green51ShortenedProfiles Green51WeightTransform
open scoped Classical Pointwise
namespace Green51EighteenSection
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem weight_three {A : Finset V} (size : A.card=18) (avoid : ¬∃ p, FlatAt A p)
    (D : Presentation A) : ∃ z ∈ dualWords D.P.ker, (supp z).card=3 := by
  classical
  have absent : Green51ShortenedProfiles.multiplicity D.P.ker 16=0 := by
    rw [Green51ShortenedProfiles.multiplicity,card_eq_zero,eq_empty_iff_forall_notMem]
    intro c hc
    have zero : syndrome (selected A c.val)=0 := congrArg Prod.snd ((D.eval c.val).symm.trans c.property)
    obtain ⟨p,hp⟩ := Green51ElevenRelations.affine_of_sixteen_sum (selected A c.val)
      ((selected_card A c.val).trans (mem_filter.mp hc).2) zero
    exact avoid ⟨p,Green51FlatSections.flat_mono (selected_sub A c.val) hp⟩
  have h := profile D.P.ker (by omega) (by omega) (le_of_eq D.rank.symm) D.allowed
  rw [absent] at h
  generalize a : Green51ShortenedProfiles.multiplicity D.P.ker 8=k at h
  generalize b : Green51ShortenedProfiles.multiplicity D.P.ker 12=j at h
  generalize d : ((dualWords D.P.ker).filter fun z => (supp z).card=3).card=m at h
  have six : m=6 := by
    simp only [size,profiles,mem_insert,mem_singleton,Prod.mk.injEq] at h
    omega
  have pos : 0<((dualWords D.P.ker).filter fun z => (supp z).card=3).card := by omega
  obtain ⟨z,hz⟩ := card_pos.mp pos
  exact ⟨z,(mem_filter.mp hz).1,(mem_filter.mp hz).2⟩

private theorem descend {n : ℕ} (P : Cube n →ₗ[F] F×V) (onto : Function.Surjective P)
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

private theorem unit_column {A : Finset V} (D : Presentation A) (i : Fin A.card) :
    D.P (Pi.single i 1)=(1,(A.equivFin.symm i).val) := by
  have hs : supp (Pi.single i (1:F))={i} := by
    ext t
    by_cases eq:t=i <;> simp [supp,Pi.single_apply,eq]
  rw [D.eval]
  simp [selected,syndrome,hs]
  rfl

/-- A hyperplane contains exactly fifteen of the eighteen labels whenever
their double has no affine three-space. Its parallel mate contains the remaining three. -/
theorem hyperplane (A : Finset V) (size : A.card=18) (avoid : ¬∃ p, FlatAt A p) :
    ∃ (L : V →ₗ[F] F) (c:F), L≠0 ∧ (A.filter (fun x => L x=c)).card=15 := by
  classical
  obtain ⟨D⟩ := presentation (by omega) (by omega) (fun h => avoid ⟨0,h⟩)
  obtain ⟨z,dual,weight⟩ := weight_three size avoid D
  obtain ⟨l,hl⟩ := descend D.P D.onto dual
  let idx (i : Fin A.card) := (A.equivFin.symm i).val
  let L := l.comp (LinearMap.inr F F V)
  let c := -l (1,0)
  have test (i : Fin A.card) : L (idx i)=c ↔ z i=0 := by
    have split : ((1:F),idx i) = (1,0)+(0,idx i) := by simp
    have eq := hl i
    rw [unit_column] at eq
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
  have card : (A.filter (fun x => L x=c)).card=15 := by
    have inj : Function.Injective idx := Subtype.val_injective.comp A.equivFin.symm.injective
    rw [cut,card_image_of_injective _ inj,
      card_compl,Fintype.card_fin,weight,size]
  refine ⟨L,c,?_,card⟩
  intro zero
  by_cases k:c=0
  · simp [zero,k,size] at card
  · simp [zero,Ne.symm k] at card

end Green51EighteenSection
#print axioms Green51EighteenSection.hyperplane
