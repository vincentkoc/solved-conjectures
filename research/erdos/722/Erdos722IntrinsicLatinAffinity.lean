import Erdos722LatinCosetSystems

/-! # The ternary affine relation intrinsic to a four-symbol alphabet -/

namespace Erdos722.AffineStar
open Equiv Finset QuadCompletion FourPoint QuadSwitch LatinFillings
open scoped Classical
noncomputable section

/-- All coordinate permutations of a four-point fibre preserve ternary addition. -/
theorem fibre_mix_perm (s : Perm Fibre) (x y z : Fibre) :
    s (x+y+z)=s x+s y+s z := by
  obtain ⟨g,eq⟩ := affine_fibre s
  rw [eq (x+y+z),eq x,eq y,eq z,move_add,move_add]
  exact (show ∀ a b c t : Fibre, a+b+c+t=(a+t)+(b+t)+(c+t) by decide +kernel) _ _ _ _

def mix (x y z : Symbol) := symbols (symbols.symm x+symbols.symm y+symbols.symm z)

theorem mix_natural (s : Perm Symbol) (x y z : Symbol) :
    s (mix x y z)=mix (s x) (s y) (s z) := by
  let e := (symbols.trans s).trans symbols.symm
  have eq := fibre_mix_perm e (symbols.symm x) (symbols.symm y) (symbols.symm z)
  apply symbols.symm.injective
  simpa only [e,mix,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.symm_apply_apply] using eq

theorem mix_symbols (x y z : Fibre) : mix (symbols x) (symbols y) (symbols z)=symbols (x+y+z) := by
  simp only [mix,Equiv.symm_apply_apply]

theorem mix_repeats (x y : Symbol) : mix x y y=x ∧ mix y x y=x ∧ mix y y x=x := by
  have eq : ∀ u v : Fibre, u+v+v=u ∧ v+u+v=u ∧ v+v+u=u := by decide +kernel
  obtain ⟨a,b,c⟩ := eq (symbols.symm x) (symbols.symm y)
  simp only [mix,a,b,c,Equiv.apply_symm_apply,and_self]

theorem mix_interchange (a b c u v w i j k : Symbol) :
    mix (mix a b c) (mix u v w) (mix i j k) =
      mix (mix a u i) (mix b v j) (mix c w k) := by
  simp only [mix,Equiv.symm_apply_apply]
  congr 1
  ac_rfl

def standardCube : Reduced := by
  refine ⟨⟨mix,?_,?_,?_⟩,fun x => mix_repeats x 0⟩
  · intro y z x x' eq
    exact symbols.symm.injective (add_right_cancel (add_right_cancel (symbols.injective eq)))
  · intro x z y y' eq
    exact symbols.symm.injective (add_left_cancel (add_right_cancel (symbols.injective eq)))
  · intro x y z z' eq
    exact symbols.symm.injective (add_left_cancel (symbols.injective eq))

abbrev Inputs := Fin 3 → Symbol

def evaluate (q : Quasigroup) (x : Inputs) := q.val (x 0) (x 1) (x 2)

/-- An affine Latin graph is closed under coordinatewise ternary addition. -/
def AffineCube (q : Quasigroup) : Prop := ∀ x y z : Inputs,
    evaluate q (fun j => mix (x j) (y j) (z j)) = mix (evaluate q x) (evaluate q y) (evaluate q z)

theorem affine_standard : AffineCube standardCube.val := fun x y z =>
  mix_interchange (x 0) (y 0) (z 0) (x 1) (y 1) (z 1) (x 2) (y 2) (z 2)

/-- Normalizing each of the three axes forces an affine cube to be ternary addition. -/
theorem reduced_affine_iff (q : Reduced) : AffineCube q.val ↔ q=standardCube := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    funext x y z
    have eq := h ![x,0,0] ![0,y,0] ![0,0,z]
    change q.val.val (mix x 0 0) (mix 0 y 0) (mix 0 0 z)=
      mix (q.val.val x 0 0) (q.val.val 0 y 0) (q.val.val 0 0 z) at eq
    exact (by simpa only [(mix_repeats x 0).1,(mix_repeats y 0).2.1,(mix_repeats z 0).2.2,
      (q.prop x).1,(q.prop y).2.1,(q.prop z).2.2] using eq : q.val.val x y z=mix x y z)
  · rintro rfl
    exact affine_standard

#print axioms fibre_mix_perm
#print axioms mix
#print axioms mix_natural
#print axioms mix_symbols
#print axioms mix_repeats
#print axioms mix_interchange
#print axioms standardCube
#print axioms Inputs
#print axioms evaluate
#print axioms AffineCube
#print axioms affine_standard
#print axioms reduced_affine_iff
end
end Erdos722.AffineStar
