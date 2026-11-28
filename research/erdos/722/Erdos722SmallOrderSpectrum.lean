import Erdos722QuadrupleSpectrum
import Erdos722SecondOrderTwentySix
import Erdos722ProjectiveSublines
import Erdos722SmallParameterTable
import Erdos722SmallWitness42

/-! # The nontrivial rank-three spectrum through order fifty -/

namespace Erdos722.SmallOrders

abbrev TripleDesign (k n : ℕ) := ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 k

/-- Parameters realized here, restricted in the spectrum theorem to 3 < k < n ≤ 50. -/
def realized (k n : ℕ) : Prop :=
  (k=4 ∧ (n%6=2 ∨ n%6=4)) ∨ (k=5 ∧ (n=17 ∨ n=26)) ∨
  (k=6 ∧ (n=22 ∨ n=26 ∨ n=42)) ∨ (k=8 ∧ n=50)

/-- The three parameters left open in the table of Kiermaier, Krčadinac and Wassermann. -/
def remaining (k n : ℕ) : Prop := (k=5 ∧ (n=41 ∨ n=50)) ∨ (k=6 ∧ n=46)

private theorem construct_realized (seed : TripleDesign 6 22) {k n : ℕ}
    (h : realized k n) : TripleDesign k n := by
  rcases h with ⟨rfl,h⟩|⟨rfl,(rfl|rfl)⟩|⟨rfl,(rfl|rfl|rfl)⟩|⟨rfl,rfl⟩
  · exact Fourfold.admissible_quadruples n h
  · exact Sublines.exists_prime_power_subline_design 2 2 2 (by decide) (by decide)
  · exact SecondOrder.order_twenty_six
  · exact seed
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact Sublines.exists_prime_power_subline_design 5 1 2 (by decide) (by decide)
  · exact Witness42.order_forty_two
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact Sublines.exists_prime_power_subline_design 7 1 2 (by decide) (by decide)

/-- Reducing the finite spectrum to three fixed incidence propositions.
The supplemental specialization discharges the two external inputs. -/
theorem spectrum_of_inputs (seed : TripleDesign 6 22)
    (seven : ∀ v, 7<v → TripleDesign 7 v → 77≤v)
    {k n : ℕ} (hk : 3<k) (hkn : k<n) (hn : n≤50) :
    TripleDesign k n ↔ realized k n ∨
      (k=5 ∧ n=41 ∧ TripleDesign 5 41) ∨ (k=6 ∧ n=46 ∧ TripleDesign 6 46) ∨
      (k=5 ∧ n=50 ∧ TripleDesign 5 50) := by
  constructor
  · intro h
    by_cases h₄ : k=4
    · subst k
      rcases (Fourfold.quadruple_spectrum n).mp h with hsmall|hr
      · omega
      · exact Or.inl (Or.inl ⟨rfl,hr⟩)
    have adm := fun i (hi : i<3) => Quartet.design_divisibility h.choose_spec (i:=i)
      (by omega) hi.le
    have candidates := (higher_admissible_iff (by omega : 4<k) hkn hn).mp adm
    rcases candidates with ⟨rfl,(rfl|rfl|rfl|rfl)⟩|⟨rfl,(rfl|rfl|rfl|rfl)⟩|
      ⟨rfl,(rfl|rfl)⟩|⟨rfl,rfl⟩
    all_goals first
      | exact Or.inl (by unfold realized; decide)
      | exact Or.inr (Or.inl ⟨rfl,rfl,h⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,h⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl,h⟩))
      | exact absurd (seven _ (by decide) h) (by decide)
  · rintro (h|⟨rfl,rfl,h⟩|⟨rfl,rfl,h⟩|⟨rfl,rfl,h⟩)
    · exact construct_realized seed h
    all_goals exact h

#print axioms TripleDesign
#print axioms realized
#print axioms remaining
#print axioms spectrum_of_inputs
end Erdos722.SmallOrders
