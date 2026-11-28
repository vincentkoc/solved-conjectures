import Erdos478QuarticRootActions
import Erdos478LowGapFrobeniusProfiles
import Erdos478PermutationCountLaw

/-! # The full joint fixed-point law in any common Galois splitting field -/

namespace Erdos478.LowGapAction
open Finset Equiv Polynomial FrobeniusCounts FirstCollision BinaryGap
local instance (n : ℕ) : Fintype (Perm (Fin n)) := fintypePerm
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable (split : ∀ k, 2≤k → k≤4 → ((rationalGap k).map (algebraMap ℚ K)).Splits)

def lawValue (a b c : ℕ → Bool) : ℝ :=
  ((binaryWeight (fun i => a i.val)*cubicWeight (fun i => b i.val)*quarticWeight (fun i => c i.val) : ℕ):ℝ)/96

include split in
theorem joint_fixed_law (a b c : ℕ → Bool) :
    uniform (Aut K) (fun g => if a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g)
      then 1 else 0)=lawValue a b c := by
  let e₂ := rootLabels K (by decide : 0<2) (split 2 (by decide) (by decide))
  let e₃ := rootLabels K (by decide : 0<3) (split 3 (by decide) (by decide))
  let e₄ := rootLabels K (by decide : 0<4) (split 4 (by decide) (by decide))
  let A := (numberedAction K e₂).prod (numberedAction K e₃)
  let B := numberedAction K e₄
  let r := pairedReflection K e₄
  obtain ⟨inv,free,comm⟩ := reflection_data K e₄
  obtain ⟨⟨u,uq,uc,ud⟩,⟨v,vc,vd⟩,⟨s,sd⟩⟩ := three_profiles K split
  let ρ := jointAction A B r comm
  have surj : Function.Surjective ρ := by
    apply joint_surjective A B r inv free comm (numbered_transitive K (by decide) e₄)
    · exact ⟨u,(numbered_fixed K e₂ u).trans uq,(numbered_fixed K e₃ u).trans uc,(numbered_fixed K e₄ u).trans ud⟩
    · exact ⟨v,(numbered_fixed K e₃ v).trans vc,(numbered_fixed K e₄ v).trans vd⟩
    · exact ⟨s,(numbered_fixed K e₄ s).trans sd⟩
  let w (q : Small × PairGroup r) : ℝ :=
    if a (pointCount q.1.1) && b (pointCount q.1.2) && c (pointCount q.2.val) then 1 else 0
  have pull := quotient_mean ρ surj w
  have eq : (fun g => w (ρ g))=(fun g => if a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g)
      then (1:ℝ) else 0) := by
    funext g
    change (if a (pointCount (numberedAction K e₂ g)) && b (pointCount (numberedAction K e₃ g)) &&
      c (pointCount (numberedAction K e₄ g)) then _ else _) = _
    rw [numbered_fixed,numbered_fixed,numbered_fixed]
  rw [eq] at pull
  exact pull.trans (model_probability r inv free (fun i => a i.val) (fun i => b i.val) (fun i => c i.val))

#print axioms lawValue
#print axioms joint_fixed_law
end
end Erdos478.LowGapAction
