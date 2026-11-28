import Green51BCHSafeThree
import Green51BCHFourForces
import Green51BCHPlateau

/-! # A 64-point example for the affine Green 51 guarantee in dimension 21 -/

open Green50Downsets Green51BCH Green51BCHCompression
open scoped Pointwise
namespace Green51BCHExceptional
local notation "F" => ZMod 2

/-- The exceptional projection fits all 64 field labels into 21 binary
coordinates, and their double contains no affine three-dimensional subspace. -/
theorem example_twenty_one :
    ∃ A : Finset (Cube 21), A.card=64 ∧ ∀ (W : Submodule F (Cube 21)) (p : Cube 21),
      p+ᵥ (W:Set (Cube 21)) ⊆ ↑(A+A) → Module.finrank F W≤2 := by
  classical
  let K := GaloisField 2 6
  let _ : Fintype K := Fintype.ofFinite K
  have dim : Module.finrank F K=6 := GaloisField.finrank 2 (by decide)
  obtain ⟨S,avoid⟩ := three_can_avoid dim
  have q := S.val.finrank_quotient_add_finrank
  rw [S.property,dim] at q
  let E : (Space K × (K ⧸ S.val)) ≃ₗ[F] Cube 21 := LinearEquiv.ofFinrankEq _ _ (by
    simp only [Space,Cube,Module.finrank_prod,Module.finrank_fin_fun,dim];omega)
  obtain ⟨A,card,free⟩ := transport_curve S.val.mkQ E avoid
  refine ⟨A,card.trans ?_,free⟩
  rw [←Nat.card_eq_fintype_card]
  exact GaloisField.card 2 6 (by decide)

/-- The pinned affine guarantee is exactly two up to density 64/2²¹. -/
theorem plateau_twenty_one {α : ℝ} (lo : 2/(2:ℝ)^21<α) (hi : α≤64/(2:ℝ)^21) :
    Green51.guaranteedMaxCosetDim 21 α=2 := by
  obtain ⟨A,sz,free⟩ := example_twenty_one
  exact plateau_of_example A free lo (by simpa [sz] using hi)

end Green51BCHExceptional
#print axioms Green51BCHExceptional.example_twenty_one
#print axioms Green51BCHExceptional.plateau_twenty_one
