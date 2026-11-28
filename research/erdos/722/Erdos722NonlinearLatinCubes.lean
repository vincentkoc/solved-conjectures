import Erdos722IntrinsicLatinAffinity

/-! # Counting the affine and nonlinear Latin graphs among all labelled cubes -/

namespace Erdos722.AffineStar
open Equiv FourPoint LatinFillings
open scoped Classical
noncomputable section

private theorem chart_forward (q r : Quasigroup) (s : Fin 3 → Perm Symbol) (v : Perm Symbol)
    (chart : ∀ x, evaluate r x=v (evaluate q (fun i => s i (x i)))) (h : AffineCube q) :
    AffineCube r := by
  intro x y z
  rw [chart,chart,chart,chart]
  have eq : (fun i => s i (mix (x i) (y i) (z i))) =
      (fun i => mix (s i (x i)) (s i (y i)) (s i (z i))) :=
    funext fun i => mix_natural (s i) _ _ _
  rw [eq,h (fun i => s i (x i)) (fun i => s i (y i)) (fun i => s i (z i)),mix_natural]

theorem chart_iff (q r : Quasigroup) (s : Fin 3 → Perm Symbol) (v : Perm Symbol)
    (chart : ∀ x, evaluate r x=v (evaluate q (fun i => s i (x i)))) :
    AffineCube r ↔ AffineCube q := by
  refine ⟨chart_forward r q (fun i => (s i).symm) v.symm ?_,chart_forward q r s v chart⟩
  intro x
  rw [chart]
  simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]

theorem affine_normalization (v : CubeParameters) :
    AffineCube (normalization.symm v) ↔ v.1=standardCube := by
  let a := v.2.2
  let s : Fin 3 → Perm Symbol := ![a.1.val,a.2.1.val,a.2.2.val]
  exact (chart_iff v.1.val (normalization.symm v) s (swap 0 v.2.1) (fun _ => rfl)).trans
    (reduced_affine_iff v.1)

abbrev AxisChoices := Symbol × (Axis × Axis × Axis)

/-- The common coordinate normal form determines the affine locus exactly. -/
def affineChoices : {q : Quasigroup // AffineCube q} ≃ AxisChoices where
  toFun q := (normalization q.val).2
  invFun a := ⟨normalization.symm (standardCube,a),(affine_normalization _).mpr rfl⟩
  left_inv q := by
    have hit := q.prop
    rw [← normalization.symm_apply_apply q.val,affine_normalization] at hit
    apply Subtype.ext
    apply normalization.injective
    rw [normalization.apply_symm_apply]
    exact Prod.ext hit.symm rfl
  right_inv a := congrArg Prod.snd (normalization.apply_symm_apply (standardCube,a))

theorem affine_cube_count : Nat.card {q : Quasigroup // AffineCube q}=864 := by
  rw [Nat.card_congr affineChoices]
  simp only [AxisChoices,Nat.card_prod,Nat.card_fin,axis_card]

theorem nonlinear_cube_count : Nat.card {q : Quasigroup // ¬AffineCube q}=54432 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,latin_cube_count,affine_cube_count]

#print axioms chart_iff
#print axioms affine_normalization
#print axioms AxisChoices
#print axioms affineChoices
#print axioms affine_cube_count
#print axioms nonlinear_cube_count
end
end Erdos722.AffineStar
