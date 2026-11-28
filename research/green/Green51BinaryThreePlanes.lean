import Green51SubspaceGrowth

/-! # Counting binary three-dimensional subspaces by ordered bases -/

namespace Green51BCHFlags
local notation "F" => ZMod 2
variable (V : Type*) [AddCommGroup V] [Module F V] [Finite V]
abbrev Planes := Green51SubspaceGrowth.Planes V 3
abbrev Frames := Green51SubspaceGrowth.Frames V 3

theorem planes_card (dim : 3≤Module.finrank F V) :
    Nat.card (Planes V)*168=∏ i : Fin 3,(2^(Module.finrank F V)-2^i.val) := by
  have count := Green51SubspaceGrowth.frame_count V dim
  have bases : (∏ i : Fin 3, (2^3-2^i.val : ℕ))=168 := by decide
  rw [bases] at count
  exact count

end Green51BCHFlags
#print axioms Green51BCHFlags.planes_card
