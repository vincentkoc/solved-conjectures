import Erdos478TetrahedralRelativeAction
import Erdos478TetrahedralEdgeCoordinates

/-! # The joint image on the actual six factorial-gap roots and all lower roots -/

namespace Erdos478.TetrahedralGap
open Polynomial Equiv FirstCollision BinaryGap LowGapAction FrobeniusCounts SplittingDensity
noncomputable section
open scoped Classical
variable (K : Type*) [Field K] [NumberField K]

abbrev edgeAction : Aut K →* Perm (GapRoots K 6) := MulAction.toPermHom _ _

/-- Two automorphisms agree on the four vertices exactly when they agree
on the six actual gap roots. -/
theorem vertex_eq_iff_edge (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits) (g h : Aut K) :
    vertexAction K g=vertexAction K h ↔ edgeAction K g=edgeAction K h := by
  have rat : (gapPoly 6).map (Int.castRingHom ℚ)=rationalGap 6 := by simp [gapPoly,rationalGap]
  have fields := common_adjoin K (quartic_splits_of_sextic K sp) (rat ▸ sp)
  rw [rat] at fields
  have eq := eqOn_of_equal_fields fields g.toAlgHom h.toAlgHom
  constructor
  · intro hv
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply eq.mp _ x.prop
    intro y hy
    exact congrArg Subtype.val (congrArg (fun π : Perm (Vertex K) => π ⟨y,hy⟩) hv)
  · intro he
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply eq.mpr _ x.prop
    intro y hy
    exact congrArg Subtype.val (congrArg (fun π : Perm (GapRoots K 6) => π ⟨y,hy⟩) he)

variable [IsGalois ℚ K]

/-- Every pair of separately attainable permutations is attained jointly,
where the first coordinate records the full tuple of lower permutations. -/
theorem exact_edge_product
    (split : ∀ k, 2≤k → k≤6 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    Function.Surjective ((lowerAction K (short 5)).rangeRestrict.prod (edgeAction K).rangeRestrict) := by
  apply RelativeGap.range_product
  intro y
  obtain ⟨g,hg⟩ := y.prop
  obtain ⟨n,hn⟩ := vertex_relative_surjective K split (vertexAction K g)
  refine ⟨n,Subtype.ext ?_⟩
  exact ((vertex_eq_iff_edge K (split 6 (by decide) (by decide)) n.val g).mp hn).trans hg

#print axioms edgeAction
#print axioms vertex_eq_iff_edge
#print axioms exact_edge_product
end
end Erdos478.TetrahedralGap
