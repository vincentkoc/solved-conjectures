import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Axis normalization for ternary quasigroups of order four -/

namespace Erdos722.LatinFillings
open Equiv
open scoped Classical
noncomputable section

abbrev Symbol := Fin 4
abbrev Table := Symbol → Symbol → Symbol → Symbol

/-- Specifying two inputs makes the remaining input a permutation. -/
def Latin (q : Table) : Prop :=
  (∀ y z, Function.Injective (fun x => q x y z)) ∧
  (∀ x z, Function.Injective (fun y => q x y z)) ∧
  (∀ x y, Function.Injective (fun z => q x y z))

abbrev Quasigroup := {q : Table // Latin q}

def Normal (q : Table) := ∀ x, q x 0 0=x ∧ q 0 x 0=x ∧ q 0 0 x=x
abbrev Reduced := {q : Quasigroup // Normal q.val}
abbrev Axis := {π : Perm Symbol // π 0=0}

private def permOf (f : Symbol → Symbol) (hf : Function.Injective f) : Perm Symbol :=
  Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩

private def chart (q : Quasigroup) (a b c d : Perm Symbol) : Quasigroup :=
  ⟨fun x y z => d (q.val (a x) (b y) (c z)),
   fun _ _ => d.injective.comp ((q.prop.1 ..).comp a.injective),
   fun _ _ => d.injective.comp ((q.prop.2.1 ..).comp b.injective),
   fun _ _ => d.injective.comp ((q.prop.2.2 ..).comp c.injective)⟩

private def axes (q : Quasigroup) : Axis × Axis × Axis :=
  let d := swap 0 (q.val 0 0 0)
  (⟨permOf _ (d.injective.comp (q.prop.1 0 0)),swap_apply_right ..⟩,
   ⟨permOf _ (d.injective.comp (q.prop.2.1 0 0)),swap_apply_right ..⟩,
   ⟨permOf _ (d.injective.comp (q.prop.2.2 0 0)),swap_apply_right ..⟩)

private theorem symm_zero (a : Axis) : a.val.symm 0=0 := a.val.symm_apply_eq.mpr a.prop.symm

private def reduce (q : Quasigroup) : Reduced := by
  let a := axes q
  let d := swap 0 (q.val 0 0 0)
  refine ⟨chart q a.1.val.symm a.2.1.val.symm a.2.2.val.symm d,?_⟩
  intro x
  change d (q.val (a.1.val.symm x) (a.2.1.val.symm 0) (a.2.2.val.symm 0))=x ∧
    d (q.val (a.1.val.symm 0) (a.2.1.val.symm x) (a.2.2.val.symm 0))=x ∧
    d (q.val (a.1.val.symm 0) (a.2.1.val.symm 0) (a.2.2.val.symm x))=x
  rw [symm_zero,symm_zero,symm_zero]
  exact ⟨a.1.val.apply_symm_apply x,a.2.1.val.apply_symm_apply x,a.2.2.val.apply_symm_apply x⟩

abbrev CubeParameters := Reduced × Symbol × (Axis × Axis × Axis)

private def expand (v : CubeParameters) := chart v.1.val v.2.2.1.val
  v.2.2.2.1.val v.2.2.2.2.val (swap 0 v.2.1)

private theorem expand_zero (v : CubeParameters) : (expand v).val 0 0 0 = v.2.1 := by
  change swap 0 v.2.1 (v.1.val.val (v.2.2.1.val 0) (v.2.2.2.1.val 0) (v.2.2.2.2.val 0))=_
  rw [v.2.2.1.prop,v.2.2.2.1.prop,v.2.2.2.2.prop,(v.1.prop 0).1,swap_apply_left]

private theorem expand_axes (v : CubeParameters) : axes (expand v)=v.2.2 := by
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    change swap 0 ((expand v).val 0 0 0) ((expand v).val x 0 0)=_
    rw [expand_zero]
    change swap 0 v.2.1 (swap 0 v.2.1 (v.1.val.val _ (v.2.2.2.1.val 0) (v.2.2.2.2.val 0)))=_
    rw [v.2.2.2.1.prop,v.2.2.2.2.prop,swap_apply_self,(v.1.prop _).1]
  · apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro x
      change swap 0 ((expand v).val 0 0 0) ((expand v).val 0 x 0)=_
      rw [expand_zero]
      change swap 0 v.2.1 (swap 0 v.2.1 (v.1.val.val (v.2.2.1.val 0) _ (v.2.2.2.2.val 0)))=_
      rw [v.2.2.1.prop,v.2.2.2.2.prop,swap_apply_self,(v.1.prop _).2.1]
    · apply Subtype.ext
      apply Equiv.ext
      intro x
      change swap 0 ((expand v).val 0 0 0) ((expand v).val 0 0 x)=_
      rw [expand_zero]
      change swap 0 v.2.1 (swap 0 v.2.1 (v.1.val.val (v.2.2.1.val 0) (v.2.2.2.1.val 0) _))=_
      rw [v.2.2.1.prop,v.2.2.2.1.prop,swap_apply_self,(v.1.prop _).2.2]

/-- One output and three independent permutations fixing zero restore the original cube. -/
def normalization : Quasigroup ≃ CubeParameters where
  toFun q := (reduce q,q.val 0 0 0,axes q)
  invFun := expand
  left_inv q := by
    apply Subtype.ext
    funext x y z
    change swap 0 _ (swap 0 _ (q.val ((axes q).1.val.symm ((axes q).1.val x))
      ((axes q).2.1.val.symm ((axes q).2.1.val y)) ((axes q).2.2.val.symm ((axes q).2.2.val z))))=_
    simp
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext x y z
      change swap 0 ((expand v).val 0 0 0) ((expand v).val
        ((axes (expand v)).1.val.symm x) ((axes (expand v)).2.1.val.symm y)
        ((axes (expand v)).2.2.val.symm z))=_
      rw [expand_zero,expand_axes]
      change swap 0 v.2.1 (swap 0 v.2.1 (v.1.val.val
        (v.2.2.1.val (v.2.2.1.val.symm x)) (v.2.2.2.1.val (v.2.2.2.1.val.symm y))
        (v.2.2.2.2.val (v.2.2.2.2.val.symm z))))=_
      simp
    · exact Prod.ext (expand_zero v) (expand_axes v)

theorem axis_card : Nat.card Axis=6 := by
  let e : Perm (Fin 3) ≃ Axis := Equiv.ofBijective
    (fun p => ⟨Perm.decomposeFin.symm (0,p),Perm.decomposeFin_symm_apply_zero ..⟩)
    (by
      constructor
      · intro p q eq
        exact (Prod.mk.inj (Perm.decomposeFin.symm.injective (congrArg Subtype.val eq))).2
      · intro a
        obtain ⟨⟨j,p⟩,eq⟩ := Perm.decomposeFin.symm.surjective a.val
        have z := Perm.decomposeFin_symm_apply_zero j p
        rw [eq,a.prop] at z
        subst j
        exact ⟨p,Subtype.ext eq⟩)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

theorem labelled_cube_count : Nat.card Quasigroup = 864*Nat.card Reduced := by
  rw [Nat.card_congr normalization]
  simp only [CubeParameters,Nat.card_prod,axis_card,Nat.card_fin]
  omega

#print axioms Latin
#print axioms Quasigroup
#print axioms Normal
#print axioms Reduced
#print axioms Axis
#print axioms CubeParameters
#print axioms normalization
#print axioms axis_card
#print axioms labelled_cube_count

end
end Erdos722.LatinFillings
