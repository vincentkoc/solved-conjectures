import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-! # The four signed sums and the six shifted coordinates generate the same field -/

namespace Erdos478.TetrahedralGap
open IntermediateField
variable {L : Type*} [Field L] [Algebra ℚ L]

def vertices (a b c : L) : Set L := {a+b+c,a-b-c,-a+b-c,-a-b+c}
def edgePoints (a b c : L) : Set L := {(5+a)/2,(5-a)/2,(5+b)/2,(5-b)/2,(5+c)/2,(5-c)/2}

theorem vertices_le (D : IntermediateField ℚ L) (a b c : L) :
    vertices a b c ⊆ D ↔ a∈D ∧ b∈D ∧ c∈D := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  simp only [vertices,Set.insert_subset_iff,Set.singleton_subset_iff,SetLike.mem_coe]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    have half {x y : L} (hx : x∈D) (hy : y∈D) := D.div_mem (D.add_mem hx hy) (D.natCast_mem 2)
    refine ⟨?_,?_,?_⟩
    · convert half h₁ h₂ using 1; ring
    · convert half h₁ h₃ using 1; ring
    · convert half h₁ h₄ using 1; ring
  · rintro ⟨ha,hb,hc⟩
    exact ⟨D.add_mem (D.add_mem ha hb) hc,D.sub_mem (D.sub_mem ha hb) hc,
      D.sub_mem (D.add_mem (D.neg_mem ha) hb) hc,D.add_mem (D.sub_mem (D.neg_mem ha) hb) hc⟩

theorem edgePoints_le (D : IntermediateField ℚ L) (a b c : L) :
    edgePoints a b c ⊆ D ↔ a∈D ∧ b∈D ∧ c∈D := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  simp only [edgePoints,Set.insert_subset_iff,Set.singleton_subset_iff,SetLike.mem_coe]
  have recover (x : L) (h : (5+x)/2∈D) : x∈D := by
    convert D.sub_mem (D.mul_mem (D.natCast_mem 2) h) (D.natCast_mem 5) using 1; ring
  have both {x : L} (h : x∈D) : (5+x)/2∈D ∧ (5-x)/2∈D :=
    ⟨D.div_mem (D.add_mem (D.natCast_mem 5) h) (D.natCast_mem 2),
      D.div_mem (D.sub_mem (D.natCast_mem 5) h) (D.natCast_mem 2)⟩
  constructor
  · rintro ⟨ha,_,hb,_,hc,_⟩
    exact ⟨recover _ ha,recover _ hb,recover _ hc⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨(both ha).1,(both ha).2,(both hb).1,(both hb).2,both hc⟩

theorem equal_spans (a b c : L) : adjoin ℚ (vertices a b c)=adjoin ℚ (edgePoints a b c) := by
  apply le_antisymm
  · apply adjoin_le_iff.mpr
    exact (vertices_le ..).mpr ((edgePoints_le ..).mp (subset_adjoin ℚ _))
  · apply adjoin_le_iff.mpr
    exact (edgePoints_le ..).mpr ((vertices_le ..).mp (subset_adjoin ℚ _))

#print axioms vertices
#print axioms edgePoints
#print axioms vertices_le
#print axioms edgePoints_le
#print axioms equal_spans
end Erdos478.TetrahedralGap
