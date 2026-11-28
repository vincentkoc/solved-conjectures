import Erdos722QuartetSeeds
import Erdos722QuartetDirections
import Erdos722QuartetTransversals

/-!
# Four ingredients for the five-point construction

Orders 21 and 25 use transversal designs with five columns. Order 41 uses two
cyclic starters; order 65 is the classical Hermitian unital of order four.
-/

namespace Erdos722.Five
open Erdos722.Quartet Erdos722.Quartet.Transversal

def Sizes (n : ℕ) := n=5 ∨ n=6 ∨ n=10 ∨ n=16

private def starters : Fin 2 → Fin 5 → ZMod 41 :=
  ![![1,10,16,18,37],![36,32,2,33,20]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem forty_one : Has (· = 5) 41 := by
  exact (ZMod.card 41) ▸ Seeds.development starters
    (by unfold Function.Injective; decide) (by unfold ExistsUnique; decide)

private theorem twenty_one : Has (· = 5) 21 := by
  classical
  let D : Directions 4 4 := Directions.primePower 4 2 2 (by decide) (by decide)
  apply (Cover.adjoin column (full D.c D.units) _).has (by simp [Point,D.card])
  let A := (Has.single (s := (· = 5)) rfl).realize (V := Option D.K) (by simp [D.card])
  intro i
  cases i with
  | none => exact A.relabel (Equiv.optionCongr lastFiber)
  | some i => exact A.relabel (Equiv.optionCongr (finiteFiber i))

private theorem twenty_five : Has (· = 5) 25 := by
  classical
  let D : Directions 4 5 := Directions.primePower 4 5 1 (by decide) (by decide)
  apply (Cover.fillFibers column (full D.c D.units) _).has (by simp [Point,D.card])
  let A := (Has.single (s := (· = 5)) rfl).realize D.card
  intro i
  cases i with
  | none => exact A.relabel lastFiber
  | some i => exact A.relabel (finiteFiber i)

theorem seed_design (s : ℕ) (hs : Sizes s) : Has (· = 5) (4*s+1) := by
  rcases hs with rfl | rfl | rfl | rfl
  · exact twenty_one
  · exact twenty_five
  · exact forty_one
  · obtain ⟨D,hD⟩ := HermitianUnital.prime_power_unital 2 2 (by decide)
    exact ⟨Cover.ofDesign hD⟩

#print axioms Erdos722.Quartet.Seeds.development
#print axioms forty_one
#print axioms seed_design

end Erdos722.Five
