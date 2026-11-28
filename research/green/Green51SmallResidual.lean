import Green51TwelveCodes

/-! # A light word in every binary length-21 code of dimension at least 13 -/

open Finset Green50Downsets Green50Sharp Green51TwelveResidual
open scoped Classical
namespace Green51SmallResidual
local notation "F" => ZMod 2

/-- A binary code of length twenty-one and dimension at least thirteen has a
nonzero word of weight at most four. -/
theorem twenty_one (C : Submodule F (Cube 21)) (rank : 13≤Module.finrank F C) :
    ∃ u:C, u≠0 ∧ (supp u.val).card≤4 := by
  classical
  have someWord : ∃ d:ℕ,∃x:C,x≠0 ∧ (supp x.val).card=d := by
    have more : Nontrivial C := Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank F C)
    obtain ⟨x,nx⟩ := exists_ne (0:C)
    exact ⟨_,x,nx,rfl⟩
  let d := Nat.find someWord
  obtain ⟨u,nz,wt⟩ : ∃u:C,u≠0 ∧ (supp u.val).card=d := Nat.find_spec someWord
  have least (x:C) (ne:x≠0) : d≤(supp x.val).card :=
    Nat.find_min' someWord ⟨x,ne,rfl⟩
  by_contra! none
  have five := none u nz
  have inequality := short_packing C least u wt (by omega) (by omega)
  let r := 21-d
  have few : r≤16 := by dsimp [r];omega
  have power : 4096≤2^(Module.finrank F C-1) :=
    Nat.pow_le_pow_right (by decide : 0<2) (show 12≤Module.finrank F C-1 by omega)
  have no : ¬4096*(r+1)≤2^r := by
    interval_cases r <;> decide
  exact no ((Nat.mul_le_mul_right (r+1) power).trans inequality)

end Green51SmallResidual
#print axioms Green51SmallResidual.twenty_one
