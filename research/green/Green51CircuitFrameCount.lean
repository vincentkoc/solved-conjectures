import Green51FrameQuotients
import Green51ExtremalPeriods
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Counting surjections to a binary cube -/
namespace Green51GirthFrame
open Finset Green53ParityThreshold
open scoped Classical
variable (G : Type*) [AddCommGroup G] [Module F G] [Fintype G]

theorem card_surjections_cube (d : ℕ) (small : d ≤ Module.finrank F G) :
    Nat.card {f : G →ₗ[F] (Fin d → F) // Function.Surjective f} =
      ∏ i : Fin d, (2^(Module.finrank F G)-2^i.val) := by
  classical
  let : Finite (Module.Dual F G) := Finite.of_injective (fun f : Module.Dual F G => (f : G → F)) DFunLike.coe_injective
  let B := (Pi.basisFun F (Fin d)).dualBasis
  have coords (i : Fin d) (w : Fin d → F) : B i w = w i := by
    rw [Module.Basis.dualBasis_apply,Pi.basisFun_repr]
  let e : {f : G →ₗ[F] (Fin d → F) // Function.Surjective f} ≃
      {a : Fin d → Module.Dual F G // LinearIndependent F a} :=
    { toFun := fun f => ⟨fun i => f.val.dualMap (B i),B.linearIndependent.map' _
          (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_iff.mpr f.property))⟩
      invFun := fun a => ⟨LinearMap.pi a.val,by
        apply LinearMap.dualMap_injective_iff.mp
        have iden : (LinearMap.pi a.val).dualMap = B.constr F a.val := by
          apply B.ext
          intro i
          rw [B.constr_basis]
          ext x
          exact coords _ _
        rw [iden]
        exact B.injective_constr_of_linearIndependent a.property⟩
      left_inv := by
        intro f
        apply Subtype.ext; ext x i
        exact coords _ _
      right_inv := by
        intro a
        apply Subtype.ext; funext i
        ext x
        exact coords _ _ }
  rw [Nat.card_congr e,card_linearIndependent]
  · simp [Subspace.dual_finrank_eq,F]
  · simpa [Subspace.dual_finrank_eq] using small
end Green51GirthFrame
#print axioms Green51GirthFrame.card_surjections_cube

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold Green51Hyperplane
open scoped Classical Pointwise

private theorem ref_exists (s : ℕ) (hs : 0<s) :
    ∃ B E : Finset (𝔽₂ (2*(s+1)+0)), ShortestOddCircuit E B ∧ B.card=2*s+3 := by
  have gap : threshold (2*s)<threshold (2*(s+1)) := by
    apply sub_pos.mp
    rw [layer_step]
    exact div_pos (halfLayer_pos _) (by positivity)
  obtain ⟨A,ha,avoid,count⟩ := (sharp_missing (s := s) (r := 0) hs gap le_rfl).1
  obtain ⟨C,m,len,_⟩ := missing_circuit (s := s) (r := 0) hs A (gap.trans_le ha) avoid count.ge
  exact ⟨C,_,m,len⟩

private theorem spanning_reference (s : ℕ) (hs : 0<s) :
    ∃ B : Finset (Fin (2*(s+1)) → F), ShortestOddCircuit B B ∧ B.card=2*s+3 ∧
      Submodule.span F (B : Set (Fin (2*(s+1)) → F)) = ⊤ := by
  obtain ⟨C,E,m,len⟩ := ref_exists s hs
  have base : ShortestOddCircuit C C := ⟨Subset.rfl,m.2.1,m.2.2.1,fun R h => m.2.2.2 R (h.trans m.1)⟩
  have hr : Module.finrank F (Submodule.span F (C : Set (𝔽₂ (2*(s+1)+0)))) + 1 = C.card := circuit_rank m
  have ht : Module.finrank F (𝔽₂ (2*(s+1)+0)) = 2*(s+1) := by simp [𝔽₂,𝔽]
  have top : Submodule.span F (C : Set (𝔽₂ (2*(s+1)+0)))=⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  exact ⟨C,base,len,top⟩
/-- The number of binary circuit frames equals the number of ordered independent rows divided by the circuit permutations. -/
theorem count_circuit_frames (G : Type*) [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (s : ℕ) (hs : 0<s) (small : 2*(s+1) ≤ Module.finrank F G) :
    (circuitFrames G (2*s+3)).card * (2*s+3).factorial =
      ∏ i : Fin (2*(s+1)), (2^(Module.finrank F G)-2^i.val) := by
  obtain ⟨B,m,size,full⟩ := spanning_reference s hs
  calc
    _ = Nat.card {f : G →ₗ[F] (Fin (2*(s+1)) → F) // Function.Surjective f} := by
      simpa only [size] using count_frame_quotients G m (by omega) full
    _ = _ := card_surjections_cube G _ small
end Green51GirthFrame
#print axioms Green51GirthFrame.count_circuit_frames
