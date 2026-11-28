import Erdos478TetrahedralStabilizers
import Erdos478QuarticRootActions

/-! # The full vertex action over every normal field splitting the sixth gap -/

namespace Erdos478.TetrahedralGap
open Polynomial IntermediateField Equiv FrobeniusCounts SplittingDensity BinaryGap LowGapAction
noncomputable section

theorem quartic_splits_of_sextic (K : Type*) [Field K] [NumberField K]
    (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits) :
    ((quartic ℚ).map (algebraMap ℚ K)).Splits := by
  let L := AlgebraicClosure ℚ
  let e : K →ₐ[ℚ] L := IsAlgClosed.lift
  let f := (gapPoly 6).map (Int.castRingHom ℚ)
  have hsp : (f.map (algebraMap ℚ K)).Splits := by simpa [f,gapPoly,rationalGap] using sp
  have hf : adjoin ℚ (f.rootSet L) ≤ e.fieldRange := by
    apply adjoin_le_iff.mpr
    rw [← hsp.image_rootSet e]
    exact fun _ ⟨x,_,hx⟩ => ⟨x,hx⟩
  have hq : adjoin ℚ ((quartic ℚ).rootSet L) ≤ e.fieldRange := (quartic_sextic_adjoin L) ▸ hf
  have hs := IntermediateField.splits_of_splits (p:=quartic ℚ) (IsAlgClosed.splits _)
    (fun x hx => hq (subset_adjoin ℚ _ hx))
  rw [quartic_map] at hs ⊢
  simpa only [quartic_map] using hs.map e.equivFieldRange.symm.toRingHom

variable (K : Type*) [Field K] [Algebra ℚ K]

abbrev Vertex := (quartic ℚ).rootSet K

def vertexAction : Aut K →* Perm (Vertex K) := MulAction.toPermHom _ _

theorem vertex_card (sp : ((quartic ℚ).map (algebraMap ℚ K)).Splits) :
    Fintype.card (Vertex K)=4 := by
  rw [card_rootSet_eq_natDegree (quartic_separable ℚ (by norm_num)) sp,quartic_degree]

theorem vertex_surjective [Normal ℚ K] (sp : ((quartic ℚ).map (algebraMap ℚ K)).Splits) :
    Function.Surjective (vertexAction K) := by
  classical
  let q := quartic ℚ
  let : Fact ((q.map (algebraMap ℚ K)).Splits) := ⟨sp⟩
  let a := Gal.galActionHom q K
  have hc : Nat.card q.Gal=Nat.card (Perm (q.rootSet K)) := by
    rw [Gal.card_of_separable (quartic_separable ℚ (by norm_num)),quartic_splitting_degree,
      Nat.card_perm,Nat.card_eq_fintype_card,vertex_card K sp]
    decide
  have onto := ((Nat.bijective_iff_injective_and_card a).mpr ⟨Gal.galActionHom_injective q K,hc⟩).2
  intro π
  obtain ⟨t,ht⟩ := onto π
  obtain ⟨g,hg⟩ := Gal.restrict_surjective q K t
  refine ⟨g,Equiv.ext fun x => Subtype.ext ?_⟩
  rw [← ht,← hg]
  exact (Gal.galActionHom_restrict q K g x).symm

#print axioms quartic_splits_of_sextic
#print axioms Vertex
#print axioms vertexAction
#print axioms vertex_card
#print axioms vertex_surjective
end
end Erdos478.TetrahedralGap
