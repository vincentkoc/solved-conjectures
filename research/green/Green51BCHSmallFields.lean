import Green51BCHThreshold
import Green51SeventhOrbit

/-! # Sharp BCH compression in every binary dimension at least four except six -/

open Green50Downsets Green51BCH
open scoped Pointwise
namespace Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

/-- In every binary field dimension at least four other than six, a projected
fourth BCH coordinate gives a three-flat in the double exactly when its
kernel has dimension at least three. -/
theorem three_iff_except_six {H : Type*} [AddCommGroup H] [Module F H]
    (L : K →ₗ[F] H) (room : 4 ≤ Module.finrank F K) (six : Module.finrank F K ≠ 6) :
    (∃ (p : Space K × H) (W : Submodule F (Space K × H)), Module.finrank F W=3 ∧
      p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L)) ↔
    3 ≤ Module.finrank F L.ker := by
  by_cases big : 10 ≤ Module.finrank F K
  · exact three_iff L (Or.inl big)
  by_cases nine : Module.finrank F K=9
  · exact three_iff_of_meeting L (fun T => Green51SeventhOrbit.seventh_meets_nine T nine)
  apply three_iff L (Or.inr ⟨room,?_⟩)
  rw [Nat.card_units,Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=F),ZMod.card]
  have cases : Module.finrank F K=4 ∨ Module.finrank F K=5 ∨
      Module.finrank F K=7 ∨ Module.finrank F K=8 := by omega
  rcases cases with d | d | d | d <;> rw [d] <;> decide

end Green51BCHCompression

#print axioms Green51BCHCompression.three_iff_except_six
