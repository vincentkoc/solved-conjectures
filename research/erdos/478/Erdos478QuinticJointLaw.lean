import Erdos478RelativeGapIndependence
import Erdos478QuinticFrobenius
import Erdos478QuinticFixedCounts
import Erdos478ExactFourthAtom

/-! # Independent quintic root permutations after conditioning on the first three gap actions -/

namespace Erdos478.QuinticLaw
open Finset Equiv Polynomial FirstCollision LowGapAction BinaryGap FrobeniusCounts RelativeGap
local instance : Fintype (Perm (Fin 5)) := fintypePerm
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable (split : ∀ k, 2≤k → k≤5 → ((rationalGap k).map (algebraMap ℚ K)).Splits)

include split in
theorem quintic_relative_surjective (e : GapRoots K 5 ≃ Fin 5) :
    Function.Surjective ((numberedAction K e).comp (LowerKernel K (short 4)).subtype) := by
  apply full_relative K _ (by decide)
  · intro k hk
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    omega
  · intro k hk
    obtain rfl|h := mem_insert.mp hk
    · exact split 5 (by decide) (by decide)
    · obtain ⟨lo,hi⟩ := mem_Icc.mp h
      exact split k lo (by omega)
  · obtain ⟨g,h₂,h₃,h₄,h₅⟩ := QuinticSample.quintic_profile K split
    refine ⟨g,?_,by omega⟩
    intro k hk
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    rcases (by omega : k=2 ∨ k=3 ∨ k=4) with rfl|rfl|rfl <;> assumption

def fourLaw (a b c f : ℕ → Bool) : ℝ :=
  lawValue a b c*((quinticWeight (fun i => f i.val) : ℕ) : ℝ)/120

include split in
/-- The four counts have independent margins, for arbitrary masks of each count. -/
theorem joint_quintic_law (a b c f : ℕ → Bool) :
    uniform (Aut K) (fun g => if a (fixedGap K 2 g) && b (fixedGap K 3 g) &&
      c (fixedGap K 4 g) && f (fixedGap K 5 g) then 1 else 0)=fourLaw a b c f := by
  let e := rootLabels K (by decide : 0<5) (split 5 (by decide) (by decide))
  let W (g : Aut K) : ℝ :=
    if a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g) then 1 else 0
  let V (g : Perm (Fin 5)) : ℝ := if f (pointCount g) then 1 else 0
  have stable (n : LowerKernel K (short 4)) (g : Aut K) : W (n.val*g)=W g := by
    simp only [W,stable_count K n g (show 2∈short 4 by decide),
      stable_count K n g (show 3∈short 4 by decide),stable_count K n g (show 4∈short 4 by decide)]
  have eq := quotient_independent _ (numberedAction K e) (quintic_relative_surjective K split e) W V stable
  have prod (g : Aut K) : W g*V (numberedAction K e g)=
      if a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g) && f (fixedGap K 5 g)
        then 1 else 0 := by
    simp only [W,V,numbered_fixed,Bool.and_eq_true]
    split_ifs <;> simp_all
  rw [show uniform (Aut K) W=lawValue a b c from joint_fixed_law K (fun k lo hi => split k lo (by omega)) a b c,
    show uniform (Perm (Fin 5)) V=_ from quintic_mean f] at eq
  simp_rw [prod] at eq
  rw [eq,fourLaw]
  ring

#print axioms quintic_relative_surjective
#print axioms fourLaw
#print axioms joint_quintic_law
end
end Erdos478.QuinticLaw
