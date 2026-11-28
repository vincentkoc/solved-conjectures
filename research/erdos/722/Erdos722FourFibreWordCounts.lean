import Erdos722FourFibreDirections
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Fixed directions of independent permutations of the three matchings -/

namespace Erdos722.FourPoint
open Finset Equiv
noncomputable section
open scoped Classical
variable {E : Type*} [Fintype E]
local instance : Fintype Colour := fintypePerm

def survivors (w : E → Colour) : Finset Direction :=
  univ.filter fun d => ∀ e, w e d=d

theorem mem_survivors (w : E → Colour) (d : Direction) :
    d∈survivors w ↔ ∀ e, w e d=d := by simp [survivors]

def wordsFixing (E : Type*) [Fintype E] (d : Direction) : Finset (E → Colour) :=
  univ.filter fun w => d∈survivors w

theorem wordsFixing_card (d : Direction) : (wordsFixing E d).card=2^Fintype.card E := by
  let eq : ↥(wordsFixing E d) ≃ {w : E → Colour // ∀ e, w e d=d} :=
    Equiv.subtypeEquivRight fun w => by simp [wordsFixing,mem_survivors]
  have two : ∀ a : Direction, Fintype.card {s : Colour // s a=a}=2 := by decide +kernel
  rw [← Fintype.card_coe,Fintype.card_congr (eq.trans (Equiv.subtypePiEquivPi (p:=fun (_ : E) (s : Colour) => s d=d))),Fintype.card_fun,two]

theorem identity_of_two {w : E → Colour} {a b : Direction} (ne : a≠b)
    (ha : a∈survivors w) (hb : b∈survivors w) : w=fun _ => 1 := by
  funext e
  exact (show ∀ s : Colour, ∀ a b : Direction, a≠b → s a=a → s b=b → s=1
    by decide +kernel) _ _ _ ne ((mem_survivors ..).mp ha e) ((mem_survivors ..).mp hb e)

theorem survivors_card (w : E → Colour) :
    (survivors w).card=if w=(fun _ => 1) then 3 else if ∃ d, d∈survivors w then 1 else 0 := by
  split_ifs with id ex
  · subst w; simp [survivors,Direction]
  · obtain ⟨d,hd⟩ := ex
    have eq : survivors w={d} := by
      ext a
      constructor
      · intro ha; exact mem_singleton.mpr (by_contra (fun ne => id (identity_of_two ne ha hd)))
      · rintro ha; rwa [mem_singleton.mp ha]
    simp [eq]
  · exact card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr fun d h => ex ⟨d,h⟩)

def oneDirectionWords (E : Type*) [Fintype E] : Finset (E → Colour) :=
  univ.biUnion fun d => (wordsFixing E d).erase (fun _ => 1)

theorem mem_oneDirectionWords (w : E → Colour) : w∈oneDirectionWords E ↔ (survivors w).card=1 := by
  simp only [oneDirectionWords,mem_biUnion,mem_univ,true_and,mem_erase,wordsFixing,mem_filter]
  rw [survivors_card]
  split_ifs <;> grind

theorem oneDirectionWords_card : (oneDirectionWords E).card=3*(2^Fintype.card E-1) := by
  unfold oneDirectionWords
  rw [card_biUnion]
  · have idmem (d : Direction) : (fun _ : E => (1 : Colour))∈wordsFixing E d := by
      simp [wordsFixing,mem_survivors]
    simp [card_erase_of_mem (idmem _),wordsFixing_card,Direction]
  · intro a _ b _ ne
    apply disjoint_left.mpr
    intro w ha hb
    have A := mem_erase.mp ha
    have B := mem_erase.mp hb
    apply A.1
    exact identity_of_two ne (mem_filter.mp A.2).2 (mem_filter.mp B.2).2

def noDirectionWords (E : Type*) [Fintype E] : Finset (E → Colour) :=
  univ \ insert (fun _ => 1) (oneDirectionWords E)

theorem mem_noDirectionWords (w : E → Colour) : w∈noDirectionWords E ↔ (survivors w).card=0 := by
  simp only [noDirectionWords,mem_sdiff,mem_univ,true_and,mem_insert,mem_oneDirectionWords,
    survivors_card]
  split_ifs <;> grind

theorem noDirectionWords_card : (noDirectionWords E).card=6^Fintype.card E-(1+3*(2^Fintype.card E-1)) := by
  have hn : (fun _ : E => (1 : Colour))∉oneDirectionWords E := by
    simp [mem_oneDirectionWords,survivors_card]
  rw [noDirectionWords,card_sdiff_of_subset (subset_univ _),card_univ,card_insert_of_notMem hn,
    oneDirectionWords_card,Fintype.card_fun]
  have six : Fintype.card Colour=6 := by decide +kernel
  rw [six,add_comm 1]

end

#print axioms survivors
#print axioms mem_survivors
#print axioms wordsFixing
#print axioms wordsFixing_card
#print axioms identity_of_two
#print axioms survivors_card
#print axioms oneDirectionWords
#print axioms mem_oneDirectionWords
#print axioms oneDirectionWords_card
#print axioms noDirectionWords
#print axioms mem_noDirectionWords
#print axioms noDirectionWords_card
end Erdos722.FourPoint
