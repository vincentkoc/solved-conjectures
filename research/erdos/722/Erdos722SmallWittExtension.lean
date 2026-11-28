import Erdos722AlltopSteinerExtension
import Erdos722PointedDesignProduct
import Erdos722RankIncidenceCertificates

/-! # The small Witt design by complementary extension

Six cyclic starters give a 4-(11,5,1) design. Its unique labelled
one-point extension is the classical 5-(12,6,1) Witt design.
-/

namespace Erdos722.SmallWitt
open Finset ComplementExtension

/-- Incidence rows of the six cyclic starters, with columns indexed first by
starter and then by the translating element in Z/11Z. -/
def rows : List ℕ := [
  39979187419003039553,6171398543167872643,12342797077745810695,24649565367062589967,
  49299113150529070110,24847278803238895677,49658546401640679546,25566127713280266484,
  51096244213141873128,28441540928460311504,56883081856920623008]

def blocks : Finset (Finset (Fin 11)) := SmallOrders.blocks rows 66

set_option maxRecDepth 10000 in
theorem design_eleven : blocks.IsBlockDesign 4 5 := by
  apply SmallOrders.design_of_tested_rows (ps:=rows) (b:=66)
  · decide +kernel
  · rfl

theorem unique_pointed_twelve :
    ∃! H : Finset (Finset (Option (Fin 11))), H.IsBlockDesign 5 6 ∧
      ∀ B : Finset (Fin 11), insert none (B.map Function.Embedding.some)∈H ↔ B∈blocks :=
  unique_steiner_extension (by decide) (by decide : Odd 5) design_eleven

theorem design_twelve : ∃ H : Finset (Finset (Fin 12)), H.IsBlockDesign 5 6 := by
  obtain ⟨H,⟨h,_⟩,_⟩ := unique_pointed_twelve
  exact ⟨_,PointedProduct.relabel_design (Fintype.equivFinOfCardEq (by simp : Fintype.card (Option (Fin 11))=12)) h⟩

/-- Alltop's extension with precisely the point types of the host statement. -/
theorem canonical_alltop {r k : ℕ} (hrk : r≤k) (he : Even r)
    (h : ∃ H : Finset (Finset (Fin (2*k+1))), H.IsBlockDesign r k) :
    ∃ G : Finset (Finset (Fin (2*k+2))), G.IsBlockDesign (r+1) (k+1) := by
  obtain ⟨H,hH⟩ := h
  let e : Option (Fin (2*k+1)) ≃ Fin (2*k+2) := Fintype.equivFinOfCardEq (by simp)
  exact ⟨_,PointedProduct.relabel_design e (extended_design (by simp) hrk he hH)⟩

/-- At odd block size, existence at the two maximal strengths is equivalent. -/
theorem canonical_iff {k : ℕ} (odd : Odd k) :
    (∃ H : Finset (Finset (Fin (2*k+1))), H.IsBlockDesign (k-1) k) ↔
      ∃ G : Finset (Finset (Fin (2*k+2))), G.IsBlockDesign k (k+1) := by
  let e : Option (Fin (2*k+1)) ≃ Fin (2*k+2) := Fintype.equivFinOfCardEq (by simp)
  apply (mendelsohn_steiner_iff (α:=Fin (2*k+1)) (by simp) odd).trans
  exact ⟨fun ⟨H,h⟩ => ⟨_,PointedProduct.relabel_design e h⟩,
    fun ⟨G,h⟩ => ⟨_,PointedProduct.relabel_design e.symm h⟩⟩

#print axioms canonical_alltop
#print axioms canonical_iff
#print axioms rows
#print axioms blocks
#print axioms design_eleven
#print axioms unique_pointed_twelve
#print axioms design_twelve
end Erdos722.SmallWitt
