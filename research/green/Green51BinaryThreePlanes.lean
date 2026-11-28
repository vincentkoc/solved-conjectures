import Mathlib

/-! # Counting binary three-dimensional subspaces by ordered bases -/

namespace Green51BCHFlags
local notation "F" => ZMod 2
variable (V : Type*) [AddCommGroup V] [Module F V] [Finite V]
abbrev Planes := {U : Submodule F V // Module.finrank F U=3}
abbrev Frames := {v : Fin 3 → V // LinearIndependent F v}

private def forget (s : Σ U : Planes V, Frames U.val) : Frames V :=
  ⟨s.1.val.subtype ∘ s.2.val,s.2.property.map' _ (Submodule.ker_subtype _)⟩

private theorem forget_span (s : Σ U : Planes V, Frames U.val) :
    Submodule.span F (Set.range (forget V s).val)=s.1.val := by
  apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr ?_)
  · rw [s.1.property,finrank_span_eq_card (forget V s).property,Fintype.card_fin]
  · rintro _ ⟨i,rfl⟩; exact (s.2.val i).property

private theorem forget_bijective : Function.Bijective (forget V) := by
  constructor
  · rintro ⟨⟨U,hU⟩,a⟩ ⟨⟨W,hW⟩,b⟩ eq
    have same : U=W := (forget_span V ⟨⟨U,hU⟩,a⟩).symm.trans
      ((congrArg (fun v : Frames V => Submodule.span F (Set.range v.val)) eq).trans
      (forget_span V ⟨⟨W,hW⟩,b⟩))
    subst W
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun (congrArg Subtype.val eq) i)
  · intro v
    let U := Submodule.span F (Set.range v.val)
    have rank : Module.finrank F U=3 := by simpa [U] using finrank_span_eq_card v.property
    let a : Fin 3 → U := fun i => ⟨v.val i,Submodule.subset_span ⟨i,rfl⟩⟩
    have li : LinearIndependent F a := (U.subtype.linearIndependent_iff U.ker_subtype).mp v.property
    exact ⟨⟨⟨U,rank⟩,⟨a,li⟩⟩,rfl⟩

theorem planes_card (dim : 3≤Module.finrank F V) :
    Nat.card (Planes V)*168=∏ i : Fin 3,(2^(Module.finrank F V)-2^i.val) := by
  classical
  let _ := Fintype.ofFinite (Planes V)
  have count := Nat.card_congr (Equiv.ofBijective (forget V) (forget_bijective V))
  have frames (U : Planes V) : Nat.card (Frames U.val)=168 := by
    rw [card_linearIndependent (by rw [U.property]),U.property,ZMod.card]
    decide
  rw [Nat.card_sigma,card_linearIndependent dim,ZMod.card] at count
  simpa only [frames,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using count

end Green51BCHFlags
#print axioms Green51BCHFlags.planes_card
