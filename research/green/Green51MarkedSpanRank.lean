import Green51ActiveRowPresentations

/-! # Counting labelled binary tuples with fixed span dimension -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

theorem marked_span_bound {Q H : Type*} [Finite Q] [AddCommGroup H] [Module F H]
    [FiniteDimensional F H] (n b d : ℕ) (hd : d≤n) (row : Q → Fin n → Fin b) (v : Q → Fin n → H)
    (rank : ∀ q,Module.finrank F (Submodule.span F (Set.range (v q)))=d)
    (sep : ∀ p q,row p=row q → (∃ u : H ≃ₗ[F] H, ∀ i,u (v p i)=v q i) → p=q) :
    Nat.card Q ≤ b^n * 2^((n-d)*d+(n-d)) := by
  classical
  let f (q : Q) := Finsupp.linearCombination F (v q)
  have ker (q : Q) : Module.finrank F (LinearMap.ker (f q))=n-d := by
    have t := (f q).finrank_range_add_finrank_ker
    have img : Module.finrank F (LinearMap.range (f q))=d := by
      change Module.finrank F (LinearMap.range (Finsupp.linearCombination F (v q)))=d
      rw [Finsupp.range_linearCombination]
      exact rank q
    rw [img] at t
    simpa using (show Module.finrank F (LinearMap.ker (f q))=Module.finrank F (Fin n →₀ F)-d by omega)
  let code (q : Q) : (Fin n → Fin b) × Green51SubspaceGrowth.Planes (Fin n →₀ F) (n-d) :=
    (row q,⟨LinearMap.ker (f q),ker q⟩)
  have inj : Function.Injective code := by
    intro p q eq
    apply sep p q (congrArg Prod.fst eq)
    apply (tuple_ker_iff (v p) (v q)).mp
    exact congrArg (fun t : (Fin n → Fin b) × Green51SubspaceGrowth.Planes (Fin n →₀ F) (n-d) => t.2.val) eq
  have size := Nat.card_le_card_of_injective code inj
  rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_fin] at size
  have upper := Green51SubspaceGrowth.rank_count_le (Fin n →₀ F) (n := n) (d := n-d) (by simp) (Nat.sub_le _ _)
  rw [Nat.sub_sub_self hd] at upper
  exact size.trans (Nat.mul_le_mul_left _ upper)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.marked_span_bound
