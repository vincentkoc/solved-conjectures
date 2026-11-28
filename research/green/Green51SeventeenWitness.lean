import Green51ShortenedFlatCounts

/-! # A maximal seventeen-point example in eleven binary dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open scoped Classical Pointwise
namespace Green51SeventeenWitness
local notation "V" => Cube 11

open Green51GolayWitnesses

private def extra : List ℕ := [843,1365,1638,1927,2032]
/-- Zero, the coordinate units and five additional binary labels. -/
def labels : Finset V := rows units ∪ rows extra
/-- Every strict superset of this avoiding example contains a linear three-space in its double. -/
theorem maximal : labels.card = 17 ∧ ¬FlatAt labels 0 ∧
    ∀ B : Finset V, labels ⊂ B → FlatAt B 0 := by
  have size : labels.card = 17 := by decide +kernel
  refine ⟨size,avoids_of_certificate extra (by decide +kernel) (by change 5 ≤ labels.card;omega),?_⟩
  intro B strict
  by_contra bad
  let T := rows [843,1365,1638,1927,2032,0,1,2,4,8]
  have ta : T ⊆ labels := by decide +kernel
  have count : T.card = 10 := by decide +kernel
  have z : syndrome T = 0 := by decide +kernel
  have sz := card_lt_card strict
  exact Green51ResidualPacking.no_ten (by omega : 18 ≤ B.card) bad (ta.trans (le_of_lt strict)) count z
end Green51SeventeenWitness
#print axioms Green51SeventeenWitness.maximal
