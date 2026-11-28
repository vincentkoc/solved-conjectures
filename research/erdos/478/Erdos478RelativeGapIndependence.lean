import Erdos478RelativePermutationCriterion
import Erdos478QuarticRootActions
import Erdos478UniformQuotientLaw

/-! # A relative symmetric-group test for prime-degree factorial gaps -/

namespace Erdos478.RelativeGap
open Polynomial Equiv Finset MulAction FirstCollision BinaryGap LowGapAction FrobeniusCounts
noncomputable section
open scoped Classical

private theorem support_count {k : ℕ} (g : Perm (Fin k)) :
    pointCount g+g.support.card=k := by
  simpa [pointCount,Perm.support] using
    (card_filter_add_card_filter_not (s:=(univ : Finset (Fin k))) (fun x => g x=x))

private theorem kernel_of_full_counts (K : Type*) [Field K] [Algebra ℚ K]
    (s : Finset ℕ) (pos : ∀ k∈s, 0<k)
    (split : ∀ k∈s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (g : Aut K) (h : ∀ k∈s, fixedGap K k g=k) : g∈LowerKernel K s := by
  apply _root_.funext
  intro i
  let e := rootLabels K (pos _ i.prop) (split _ i.prop)
  have count := (numbered_fixed K e g).trans (h _ i.prop)
  have size := support_count (numberedAction K e g)
  have id := Perm.support_eq_empty_iff.mp (card_eq_zero.mp (show
      (numberedAction K e g).support.card=0 by omega))
  apply Perm.ext
  intro x
  apply e.injective
  change e (g • x)=e x
  simpa only [numbered_apply,e.symm_apply_apply,Perm.one_apply] using
    congrArg (fun a : Perm (Fin i.val) => a (e x)) id

/-- The lower actions may include composite gaps. A single element fixing
every lower root and exactly all but two new roots supplies the missing swap. -/
theorem full_relative (K : Type*) [Field K] [Algebra ℚ K] [Normal ℚ K]
    (s : Finset ℕ) {l : ℕ} (hl : l.Prime) (small : ∀ k∈s, 0<k ∧ k<l)
    (split : ∀ k∈insert l s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (e : GapRoots K l ≃ Fin l) (sample : ∃ g : Aut K,
      (∀ k∈s, fixedGap K k g=k) ∧ fixedGap K l g+2=l) :
    Function.Surjective ((numberedAction K e).comp (LowerKernel K s).subtype) := by
  obtain ⟨g,low,high⟩ := sample
  let n : LowerKernel K s := ⟨g,kernel_of_full_counts K s (fun k h => (small k h).1)
    (fun k h => split k (mem_insert_of_mem h)) _ low⟩
  apply surjective_of_swap (s:=n)
  · simpa using hl
  · intro x y
    obtain ⟨m,hm⟩ := lower_transitive K s hl small split (e.symm x) (e.symm y)
    exact ⟨m,(congrArg e hm).trans (e.apply_symm_apply y)⟩
  · change (numberedAction K e g).IsSwap
    apply Perm.card_support_eq_two.mp
    have size := support_count (numberedAction K e g)
    rw [numbered_fixed] at size
    omega

/-- An arbitrary observation of the new permutation is independent of every
weight constant on the lower-action cosets. -/
theorem quotient_independent {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (N : Subgroup G) [Fintype N] (rho : G →* H)
    (full : Function.Surjective (rho.comp N.subtype)) (W : G → ℝ) (V : H → ℝ)
    (stable : ∀ (n : N) g, W (n.val*g)=W g) :
    uniform G (fun g => W g*V (rho g))=uniform H V*uniform G W := by
  apply weighted_coset N W (fun g => V (rho g)) _ stable
  intro g
  have h := quotient_mean (rho.comp N.subtype) full (fun y => V (y*rho g))
  simp only [map_mul]
  refine h.trans ?_
  change (∑ y, V (y*rho g))/_=(∑ y, V y)/_
  rw [show (∑ y, V (y*rho g))=∑ y, V y from Equiv.sum_comp (Equiv.mulRight _) V]

#print axioms full_relative
#print axioms quotient_independent
end
end Erdos478.RelativeGap
