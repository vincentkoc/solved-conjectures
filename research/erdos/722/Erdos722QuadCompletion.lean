import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-!
# Quadruple systems from ternary completions

A symmetric ternary operation with repeated-point and cancellation identities
determines a Steiner quadruple system. Embeddings preserving the operation
preserve blocks.
-/

namespace Erdos722.QuadCompletion
open Finset
variable {V : Type*} [DecidableEq V]

/-- A symmetric ternary operation with the repeated-point and cancellation
identities of a Steiner quadruple system. -/
structure Rule (V : Type*) where
  complete : V → V → V → V
  swap₁ (a b c) : complete a b c = complete b a c
  swap₂ (a b c) : complete a b c = complete a c b
  repeated (a b) : complete a a b = b
  cancel (a b c) : complete a b (complete a b c) = c

namespace Rule

variable (Q : Rule V)

omit [DecidableEq V] in
private theorem middle (a b : V) : Q.complete a b a = b := by
  rw [Q.swap₂,Q.repeated]

omit [DecidableEq V] in
private theorem lastPair (a b : V) : Q.complete a b b = a := by
  rw [Q.swap₁,middle]

theorem fresh {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Q.complete a b c ∉ ({a,b,c} : Finset V) := by
  simp only [mem_insert,mem_singleton,not_or]
  refine ⟨fun h => hbc ?_, fun h => hac ?_, fun h => hab ?_⟩
  · simpa only [h,middle] using Q.cancel a b c
  · simpa only [h,lastPair] using Q.cancel a b c
  · have hw := (Q.swap₂ a c b).trans h
    simpa only [hw,lastPair] using Q.cancel a c b

private def quad (a b c : V) : Finset V := insert (Q.complete a b c) {a,b,c}

private theorem closed (a b c : V) {x y z : V}
    (hx : x ∈ quad Q a b c) (hy : y ∈ quad Q a b c) (hz : z ∈ quad Q a b c) :
    Q.complete x y z ∈ quad Q a b c := by
  simp only [quad,mem_insert,mem_singleton] at *
  generalize he : Q.complete a b c = d at *
  have h₁ : Q.complete a b d = c := he ▸ Q.cancel a b c
  have h₂ : Q.complete a c d = b := by
    rw [← he,← Q.swap₂ a c b,Q.cancel]
  have h₃ : Q.complete b c d = a := by
    have h : Q.complete b c a = d := (Q.swap₂ b c a).trans ((Q.swap₁ b a c).trans he)
    rw [← h,Q.cancel]
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    rcases hz with rfl|rfl|rfl|rfl <;>
    grind only [= Q.swap₁,= Q.swap₂,= Q.repeated,= middle,= lastPair]

variable [Fintype V]

/-- The closed four-sets of the ternary operation. -/
noncomputable def blocks : Finset (Finset V) := by
  classical
  exact univ.filter fun B => B.card = 4 ∧ ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, Q.complete a b c ∈ B

theorem mem_blocks (B : Finset V) : B ∈ Q.blocks ↔
    B.card = 4 ∧ ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, Q.complete a b c ∈ B := by
  classical
  simp [blocks]

theorem isBlockDesign : Q.blocks.IsBlockDesign 3 4 := by
  classical
  refine ⟨fun B hB => ((mem_blocks Q B).mp hB).1, ?_⟩
  intro T hT
  obtain ⟨a,b,c,hab,hac,hbc,he⟩ := card_eq_three.mp hT
  subst T
  have h4 : (quad Q a b c).card = 4 := by
    rw [quad,card_insert_of_notMem (fresh Q hab hac hbc),hT]
  refine ⟨quad Q a b c,⟨(mem_blocks Q _).mpr ⟨h4,fun _ hx _ hy _ hz => closed Q a b c hx hy hz⟩,
    subset_insert _ _⟩,?_⟩
  rintro B ⟨hB,hs⟩
  obtain ⟨hcard,hclose⟩ := (mem_blocks Q _).mp hB
  symm
  apply eq_of_subset_of_card_le
  · apply insert_subset _ hs
    exact hclose a (hs (by simp)) b (hs (by simp)) c (hs (by simp))
  · rw [hcard,h4]

/-- An embedding preserving completions maps every block to a block. -/
theorem map_block {W : Type*} [DecidableEq W] [Fintype W] (R : Rule W) (j : V ↪ W)
    (hm : ∀ a b c, j (Q.complete a b c) = R.complete (j a) (j b) (j c))
    {B : Finset V} (hB : B ∈ Q.blocks) : B.map j ∈ R.blocks := by
  obtain ⟨hc,hq⟩ := (mem_blocks Q B).mp hB
  refine (mem_blocks R _).mpr ⟨by rwa [card_map], ?_⟩
  intro x hx y hy z hz
  obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
  obtain ⟨c,hc,rfl⟩ := mem_map.mp hz
  rw [← hm]
  exact mem_map.mpr ⟨_, hq a ha b hb c hc, rfl⟩

#print axioms isBlockDesign
#print axioms map_block

end Rule
end Erdos722.QuadCompletion
