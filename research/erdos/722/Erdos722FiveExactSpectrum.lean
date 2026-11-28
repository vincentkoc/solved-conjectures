import Erdos722FiveFiniteReduction
import Erdos722FiveDifferenceSeeds
import Erdos722FiveRelativeSeeds
import Erdos722FiveLatinSeeds
import Erdos722FiveSpectrum

/-!
# The exact spectrum of Steiner pair designs with blocks of size five

The nonempty orders are precisely those congruent to one or five modulo
twenty. The empty vertex set also satisfies the upstream predicate.
-/

namespace Erdos722.Five.Exact
open Erdos722.Quartet Filter

/-- A block of this size can be replaced by a five-point pair design after
inflating its points by four and adjoining the common point. -/
private def Local (s : ℕ) : Prop := Has (· = 5) (4*s+1)

private theorem elementary {i : ℕ} (h : Sizes i) : Local i := seed_design i h

private theorem local_five : Local 5 := elementary (by simp [Sizes])
private theorem local_six : Local 6 := elementary (by simp [Sizes])
private theorem local_ten : Local 10 := elementary (by simp [Sizes])
private theorem local_eleven : Local 11 := Relative.order45
private theorem local_fifteen : Local 15 := Starter.order61
private theorem local_sixteen : Local 16 := elementary (by simp [Sizes])

private theorem five_blocks {n : ℕ} (h : Has (· = 5) n) : Has Local n :=
  h.mono (by rintro _ rfl; exact local_five)

private theorem ten_columns {r : ℕ} (hr : r≤11) (h : Local r) : Has Local (110+r) :=
  truncate_with (a := 0) (Directions.primePower 10 11 1 (by decide) (by decide))
    local_ten local_eleven hr (by decide) (Has.single local_eleven) (Has.single h)

private theorem master_seeds (u : ℕ) (hu : u ∈ exactSeeds) : Has Local u := by
  by_cases h : u≤1
  · exact ⟨Cover.empty (fun x y hxy _ => hxy (Fin.ext (by omega)))⟩
  simp only [exactSeeds,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact Has.single local_five
  · exact Has.single local_six
  · exact Has.single local_ten
  · exact Has.single local_eleven
  · exact Has.single local_fifteen
  · exact Has.single local_sixteen
  · exact Has.single Starter.order81
  · exact five_blocks local_five
  · exact Has.single Starter.order141
  · exact Has.single Relative.order145
  · exact Has.single Starter.order161
  · exact five_blocks forty_one
  · exact five_blocks Relative.order45
  · exact Has.single Starter.order281
  · exact Array.columns14 local_five (Has.single local_fifteen)
  · exact Array.columns15 (a := 0) local_five (by decide) (Has.single local_fifteen)
  · exact Array.columns15 (a := 1) local_five (by decide) (Has.single local_sixteen)
  · exact ten_columns (r := 6) (by decide) local_six
  · exact ten_columns (r := 10) (by decide) local_ten
  · exact ten_columns (r := 11) (by decide) local_eleven

/-- Every admissible group count has a master whose blocks admit local inflation. -/
private theorem all_masters (u : ℕ) (hu : u%5≤1) : Has Local u :=
  all_orders_from_seeds (Has Local) master_seeds
    (fun _ _ _ ht hr ha => truncate_with (directions ht).some local_five local_six hr ha) u hu

theorem of_residues {n : ℕ} (h : n%20=1 ∨ n%20=5) :
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5 := by
  let u := (n-1)/4
  have hu : u%5≤1 := by dsimp [u]; omega
  have he : 4*u+1=n := by dsimp [u]; omega
  have hd := inflate_uniform (by decide : 0<4) (all_masters u hu).some (fun _ h => h)
  rw [Fintype.card_fin,he] at hd
  exact hd.some.design

/-- The exact pinned pair-design predicate, including its vacuous order zero. -/
theorem five_spectrum (n : ℕ) :
    (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5) ↔
      n=0 ∨ n%20=1 ∨ n%20=5 := by
  constructor
  · rintro ⟨H,hH⟩
    by_cases hn : n=0
    · exact Or.inl hn
    · exact Or.inr (residues (by omega) (fun i hi => design_divisibility hH (by omega) (by omega)))
  · rintro (rfl | h)
    · refine ⟨∅,fun _ he => (Finset.notMem_empty _ he).elim,?_⟩
      intro T ht
      have he := Finset.card_le_univ T
      simp only [Fintype.card_fin] at he
      omega
    · exact of_residues h

/-- For this specialization the original divisibility hypotheses suffice at
every order, even before taking the eventual filter. -/
theorem five_of_divisibility (n : ℕ)
    (h : ∀ i < 2, (5-i).choose (2-i) ∣ (n-i).choose (2-i)) :
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5 := by
  apply (five_spectrum n).mpr
  by_cases hn : n=0
  · exact Or.inl hn
  · exact Or.inr (residues (by omega) h)

theorem five_iff_divisibility (n : ℕ) :
    (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5) ↔
      ∀ i < 2, (5-i).choose (2-i) ∣ (n-i).choose (2-i) := by
  refine ⟨?_,five_of_divisibility n⟩
  rintro ⟨H,hH⟩ i hi
  by_cases hn : n=0
  · subst n
    interval_cases i <;> decide
  · exact design_divisibility hH (by omega) hi.le

#print axioms five_iff_divisibility
#print axioms master_seeds
#print axioms all_masters
#print axioms of_residues
#print axioms five_spectrum
#print axioms five_of_divisibility

end Erdos722.Five.Exact
