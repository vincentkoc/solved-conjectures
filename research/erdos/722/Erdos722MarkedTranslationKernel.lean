import Erdos722MarkedIncidence
import Erdos722AffineAnchorTranslations
import Erdos722FourFibreLabelled

/-! # The kernel of a sparsely marked binary incidence matrix -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

private theorem ordinary_on_anchor {Q : Rule I} {A : Finset I} (m : A → Q.blocks) (c : A → Colour)
    {o : I} (ho : o∉markedSupport m) (t : I → Fibre)
    (zero : weightedGradient Q (markedColours m c) t=0) (i j : I) :
    t (Q.complete i j o)=t i+t j+t o := by
  have clear (B : Q.blocks) (inside : o∈B.val) : blockGradient Q t B=0 := by
    have same : weightedGradient Q (markedColours m c) t B=blockGradient Q t B := by
      apply sum_congr rfl
      intro a _
      rw [markedColour_outside m c ho B inside a,move_one]
    exact same.symm.trans (congrFun zero B)
  have value : transversalOffset Q (blockGradient Q t) i j o=0 := by
    unfold transversalOffset offsetAt
    split
    · exact clear _ (by simp)
    · rfl
  have eq := offset_gradient Q t i j o
  rw [value] at eq
  exact (show ∀ a b : Fibre, 0=a+b → b=a by decide +kernel) _ _ eq

/-- The ordinary affine condition and the fixed-vector conditions at the marked
points are jointly necessary and sufficient for a fibre translation to fix the offsets. -/
theorem marked_kernel_iff {d : ℕ} [DecidableEq (Cube d)] {A : Finset (Cube d)}
    {m : A → (cubeRule d).blocks} (inj : Function.Injective m) (inc : ∀ q : A, q.val∈(m q).val)
    (c : A → Colour) {o : Cube d} (outside : o∉markedSupport m) (t : Cube d → Fibre) :
    weightedGradient (cubeRule d) (markedColours m c) t=0 ↔
      Offset (cubeRule d) t ∧ ∀ q : A, move (c q) (t q)=t q := by
  let Q := cubeRule d
  have standard (law : Offset Q t) : blockGradient Q t=0 := by
    change t∈(blockGradient Q).ker
    rw [gradient_kernel]
    exact law
  constructor
  · intro zero
    have law := offset_of_anchor o t (ordinary_on_anchor m c outside t zero)
    refine ⟨law,fun q => ?_⟩
    have eq := weighted_mark_difference inj c t q (inc q)
    rw [zero,standard law] at eq
    exact (show ∀ a b : Fibre, 0+0=a+b → a=b by decide +kernel) _ _ eq
  · rintro ⟨law,fixed⟩
    have ordinary := standard law
    funext B
    by_cases hit : ∃ q : A, m q=B
    · obtain ⟨q,rfl⟩ := hit
      have eq := weighted_mark_difference inj c t q (inc q)
      rw [ordinary,fixed,fibre_double] at eq
      simpa only [Pi.zero_apply,add_zero] using eq
    · have id (i : Cube d) : markedColours m c B i=1 := by
        unfold markedColours
        split
        · exact if_neg fun eq => hit ⟨_,eq⟩
        · rfl
      have same : weightedGradient Q (markedColours m c) t B=blockGradient Q t B := by
        apply sum_congr rfl
        intro i _
        rw [id,move_one]
      exact same.trans (congrFun ordinary B)

theorem basis_cycle_kernel {d : ℕ} [DecidableEq (Cube d)]
    {m : affineBasisMarks d → (cubeRule d).blocks} (inj : Function.Injective m)
    (inc : ∀ q : affineBasisMarks d, q.val∈(m q).val) {o : Cube d} (outside : o∉markedSupport m)
    {t : Cube d → Fibre} (zero : weightedGradient (cubeRule d) (markedColours m fun _ => threeCycle) t=0) :
    t=0 := by
  obtain ⟨law,h⟩ := (marked_kernel_iff inj inc (fun _ => threeCycle) outside t).mp zero
  exact offset_zero_on_basis law fun i hi =>
    (show ∀ x : Fibre, move threeCycle x=x → x=0 by decide +kernel) _ (h ⟨i,hi⟩)

#print axioms marked_kernel_iff
#print axioms basis_cycle_kernel
end
end Erdos722.FourPoint
