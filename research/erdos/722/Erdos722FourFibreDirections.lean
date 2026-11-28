import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic
/-! # Directions of the four-point fibre in a Steiner quadruple system -/
namespace Erdos722.FourPoint
open Finset Equiv
abbrev Fibre := ZMod 2 × ZMod 2
abbrev Direction := Fin 3
abbrev Colour := Perm Direction
local instance : Fintype Colour := fintypePerm
def vector : Direction → Fibre := ![(1,0),(0,1),(1,1)]
def direction (x : Fibre) : Direction := if x.1=0 then 1 else if x.2=0 then 0 else 2
def move (s : Colour) (x : Fibre) := if x=0 then 0 else vector (s (direction x))

theorem vector_ne : ∀ i, vector i≠0 := by decide +kernel
theorem direction_vector : ∀ i, direction (vector i)=i := by decide +kernel
theorem move_vector : ∀ s i, move s (vector i)=vector (s i) := by decide +kernel
theorem move_add : ∀ s x y, move s (x+y)=move s x+move s y := by decide +kernel
theorem move_inv : ∀ s x, move s⁻¹ (move s x)=x := by decide +kernel
theorem move_zero (s) : move s 0=0 := if_pos rfl

/-- The zero character, or the character whose kernel has the indicated direction. -/
def character : Option Direction → Fibre → ZMod 2
  | none, _ => 0
  | some d, x => if x=0 ∨ x=vector d then 0 else 1

theorem character_add : ∀ c x y, character c (x+y)=character c x+character c y := by
  decide +kernel

theorem character_zero : ∀ c, character c 0=0 := by decide +kernel

theorem character_injective : Function.Injective character := by
  intro c c' eq
  have h : ∀ c c', character c (1,0)=character c' (1,0) →
      character c (0,1)=character c' (0,1) → c=c' := by decide +kernel
  exact h _ _ (congrFun eq _) (congrFun eq _)

theorem character_exists (g : Fibre → ZMod 2) (h0 : g 0=0)
    (ha : ∀ x y, g (x+y)=g x+g y) : ∃ c, character c=g := by
  obtain ⟨c,hx,hy⟩ := (show ∀ a b : ZMod 2, ∃ c, character c (1,0)=a ∧
    character c (0,1)=b by decide +kernel) (g (1,0)) (g (0,1))
  refine ⟨c,funext fun x => ?_⟩
  rcases (show ∀ x : Fibre, x=0 ∨ x=(1,0) ∨ x=(0,1) ∨ x=(1,0)+(0,1)
    by decide +kernel) x with rfl|rfl|rfl|rfl
  · exact (character_zero c).trans h0.symm
  · exact hx
  · exact hy
  · rw [character_add,ha,hx,hy]

theorem character_move : ∀ s c, (∀ x, character c (move s x)=character c x) ↔
    c.map s=c := by decide +kernel

theorem move_one : ∀ x, move 1 x=x := by decide +kernel

theorem fibre_double : ∀ x : Fibre, x+x=0 := by decide +kernel

#print axioms vector
#print axioms direction
#print axioms move
#print axioms vector_ne
#print axioms direction_vector
#print axioms move_vector
#print axioms move_add
#print axioms move_inv
#print axioms move_zero
#print axioms character
#print axioms character_add
#print axioms character_zero
#print axioms character_injective
#print axioms character_exists
#print axioms character_move
#print axioms move_one
#print axioms fibre_double
end Erdos722.FourPoint
