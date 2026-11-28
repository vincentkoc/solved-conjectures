import Erdos478TetrahedralRootFields
import Erdos478IntegerGapObservables

/-! # Equal pointwise stabilizers of the edge and vertex root sets -/

namespace Erdos478.TetrahedralGap
open Polynomial IntermediateField SplittingDensity FrobeniusCounts
noncomputable section

theorem common_adjoin (K : Type*) [Field K] [NumberField K]
    (qsplit : ((quartic ℚ).map (algebraMap ℚ K)).Splits)
    (fsplit : (((gapPoly 6).map (Int.castRingHom ℚ)).map (algebraMap ℚ K)).Splits) :
    adjoin ℚ ((quartic ℚ).rootSet K)=adjoin ℚ (((gapPoly 6).map (Int.castRingHom ℚ)).rootSet K) := by
  let e : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  apply IntermediateField.map_injective e
  rw [adjoin_map,adjoin_map,qsplit.image_rootSet e,fsplit.image_rootSet e]
  exact quartic_sextic_adjoin _

theorem eqOn_of_equal_fields {K : Type*} [Field K] [Algebra ℚ K] {S T : Set K}
    (same : adjoin ℚ S=adjoin ℚ T) (g h : K →ₐ[ℚ] K) :
    Set.EqOn g h S ↔ Set.EqOn g h T := by
  let D : IntermediateField ℚ K := (AlgHom.equalizer g h).toIntermediateField fun x hx => by
    change g x=h x at hx
    change g x⁻¹=h x⁻¹
    simp only [map_inv₀,hx]
  change S⊆D ↔ T⊆D
  rw [← adjoin_le_iff,← adjoin_le_iff,same]

#print axioms common_adjoin
#print axioms eqOn_of_equal_fields
end
end Erdos478.TetrahedralGap
