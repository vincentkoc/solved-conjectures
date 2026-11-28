import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-!
# The two transversal quadruple families over a four-element base

Each parity class has eight sections of the four two-point fibres. Three
points in distinct fibres determine one section of each parity.
-/

namespace Erdos722.QuadSwitch
open Finset

abbrev Label := Fin 4 × Bool

def sectionBlock (a b c d : Bool) : Finset Label :=
  {(0,a),(1,b),(2,c),(3,d)}

def sheets (parity : Bool) : Finset (Finset Label) :=
  univ.image fun v : Bool × Bool × Bool =>
    sectionBlock v.1 v.2.1 v.2.2 (parity ^^ v.1 ^^ v.2.1 ^^ v.2.2)

theorem sheets_card : ∀ parity, (sheets parity).card = 8 := by decide +kernel

theorem sheets_disjoint : Disjoint (sheets false) (sheets true) := by decide +kernel

theorem sheet_shape {parity : Bool} {D : Finset Label} (h : D ∈ sheets parity) :
    D.card = 4 ∧ D.image Prod.fst = univ := by
  obtain ⟨⟨a,b,c⟩,_,rfl⟩ := mem_image.mp h
  revert parity a b c
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem sheet_triple : ∀ (parity : Bool) (T : Finset Label), T.card = 3 →
    (T.image Prod.fst).card = 3 → ((sheets parity).filter (T ⊆ ·)).card = 1 := by
  decide +kernel

/-- All sixteen transversals occur on one of the two sides. -/
theorem section_exhaust : ∀ D : Finset Label, D.card = 4 → D.image Prod.fst = univ →
    D ∈ sheets false ∪ sheets true := by decide +kernel

#print axioms sheets_card
#print axioms sheets_disjoint
#print axioms sheet_shape
#print axioms sheet_triple

end Erdos722.QuadSwitch
