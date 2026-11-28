import Erdos722LatinCosetSystems

/-! # The exterior weighted equations already distinguish every fibre translation -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

def exteriorGradient (d : ℕ) (hd : 6≤d) (t : Base d → Fibre) : OutsideOffsets d :=
  fun B => weightedGradient (cubeRule (d+2)) (colours d hd) t ⟨B.val,(mem_sdiff.mp B.prop).1⟩

theorem exterior_kernel (d : ℕ) (hd : 6≤d) (t : Base d → Fibre) (zero : exteriorGradient d hd t=0) : t=0 := by
  let Q := cubeRule (d+2)
  let C := colours d hd
  obtain ⟨o,clear,_⟩ := coset_common_anchor d hd (Equiv.refl _)
  have outside (B : Q.blocks) (off : B.val ∉ region d) : weightedGradient Q C t B=0 :=
    congrFun zero (⟨B.val,mem_sdiff.mpr ⟨B.prop,off⟩⟩ : outsideBlocks d)
  have plainAt (B : Q.blocks) (ho : o∈B.val) : blockGradient Q t B=0 := by
    have off : B.val∉region d := fun h => clear (mem_union_left _ (region_points d h ho))
    have same : weightedGradient Q C t B=blockGradient Q t B := by
      apply sum_congr rfl
      intro i _
      have eq := markedColour_outside (cubePrivateBlocks (d+2) (by omega)) (fun _ => threeCycle)
        (fun h => clear (mem_union_right _ h)) B ho i
      rw [show C B i=1 from eq,move_one]
    exact same.symm.trans (outside B off)
  have affine : Offset Q t := by
    apply offset_of_anchor o t
    intro i j
    have value : transversalOffset Q (blockGradient Q t) i j o=0 := by
      unfold transversalOffset offsetAt
      split
      · exact plainAt _ (by simp)
      · rfl
    have eq := offset_gradient Q t i j o
    rw [value] at eq
    exact (show ∀ x y : Fibre, 0=x+y → y=x by decide +kernel) _ _ eq
  have ord : blockGradient Q t=0 := by
    change t∈(blockGradient Q).ker
    rw [gradient_kernel]
    exact affine
  apply cycle_gradient_injective (d+2) (by omega)
  rw [map_zero]
  funext B
  by_cases inside : B.val∈region d
  · have eq : weightedGradient Q C t B=blockGradient Q t B := by
      apply sum_congr rfl
      intro x hx
      have clean := coset_avoids_basis d (region_points d inside hx)
      simp only [C,cycleCoefficients,markedColours,dif_neg clean,move_one]
    exact eq.trans (congrFun ord B)
  · exact outside B inside

theorem exterior_injective (d : ℕ) (hd : 6≤d) : Function.Injective (exteriorGradient d hd) := by
  intro t u eq
  apply sub_eq_zero.mp
  apply exterior_kernel d hd
  funext B
  have h := congrFun eq B
  change weightedGradient _ _ (t-u) _=0
  rw [map_sub]
  exact sub_eq_zero.mpr h

#print axioms exteriorGradient
#print axioms exterior_kernel
#print axioms exterior_injective
end
end Erdos722.LatinFillings
