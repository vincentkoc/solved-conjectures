import Erdos722CosetCoefficientPatterns

/-! # Trivial translation kernel for every linear filling on the reserved coset -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

abbrev cosetGradient (d : ℕ) (hd : 6≤d) (c : CosetPattern d) :=
  weightedGradient (cubeRule (d+2)) (cosetColours d hd c)

/-- A clean point forces all translations preserving the weighted equations to
be affine on the whole base, including the four-sets with variable charts. -/
theorem coset_kernel_affine (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (t : Cube (d+2) → Fibre)
    (zero : cosetGradient d hd c t=0) : Offset (cubeRule (d+2)) t := by
  let Q := cubeRule (d+2)
  obtain ⟨o,clear,_⟩ := coset_common_anchor d hd (Equiv.refl _)
  apply offset_of_anchor o t
  intro i j
  have vanish (B : Q.blocks) (inside : o∈B.val) : blockGradient Q t B=0 := by
    have same : cosetGradient d hd c t B=blockGradient Q t B := by
      apply sum_congr rfl
      intro a _
      rw [coset_colours_at_clean d hd c clear B inside a,move_one]
    exact same.symm.trans (congrFun zero B)
  have value : transversalOffset Q (blockGradient Q t) i j o=0 := by
    unfold transversalOffset offsetAt
    split
    · exact vanish _ (by simp)
    · rfl
  have eq := offset_gradient Q t i j o
  rw [value] at eq
  exact (show ∀ a b : Fibre, 0=a+b → b=a by decide +kernel) _ _ eq

theorem coset_kernel_zero (d : ℕ) (hd : 6≤d) (c : CosetPattern d) (t : Cube (d+2) → Fibre)
    (zero : cosetGradient d hd c t=0) : t=0 := by
  let Q := cubeRule (d+2)
  let D := cycleCoefficients (d+2) (by omega)
  have ordinary : blockGradient Q t=0 := by
    change t∈(blockGradient Q).ker
    rw [gradient_kernel]
    exact coset_kernel_affine d hd c t zero
  apply cycle_gradient_injective (d+2) (by omega)
  rw [map_zero]
  funext B
  by_cases hit : B∈cosetBlocks d
  · have same : weightedGradient Q D t B=blockGradient Q t B := by
      apply sum_congr rfl
      intro a ha
      have off := coset_avoids_basis d (coset_block_points d hit ha)
      simp only [D,cycleCoefficients,markedColours,dif_neg off,move_one]
    exact same.trans (congrFun ordinary B)
  · have same : weightedGradient Q D t B=cosetGradient d hd c t B := by
      apply sum_congr rfl
      intro a _
      rw [cosetColours,dif_neg hit]
    exact same.trans (congrFun zero B)

theorem coset_gradient_injective (d : ℕ) (hd : 6≤d) (c : CosetPattern d) :
    Function.Injective (cosetGradient d hd c) := by
  intro t v h
  apply sub_eq_zero.mp
  apply coset_kernel_zero d hd c
  rw [map_sub,h,sub_self]

#print axioms cosetGradient
#print axioms coset_kernel_affine
#print axioms coset_kernel_zero
#print axioms coset_gradient_injective
end
end Erdos722.FourPoint
