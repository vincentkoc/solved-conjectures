import Erdos478FiniteRootProfile
import Erdos478LowGapBezout

/-! # Three modular witnesses for the joint Galois action on gaps two to four -/

namespace Erdos478.LowGapAction
open Polynomial Finset LocalWitness SplittingDensity FrobeniusCounts FirstCollision BinaryGap RootMoments
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable (split : ∀ k, 2≤k → k≤4 → ((rationalGap k).map (algebraMap ℚ K)).Splits)

include split

private theorem modular_profile (p : ℕ) [Fact p.Prime]
    (reg : ∀ k, 2≤k → k≤4 → ¬p∣(lowCertificate k).1) :
    ∃ g : Aut K, ∀ k, 2≤k → k≤4 → fixedGap K k g=(rawRoots p k).card := by
  obtain ⟨g,hg⟩ := simultaneous_witness K p
  refine ⟨g,fun k lo hi => ?_⟩
  let f := gapPoly k
  have pos : 0<k := by omega
  have rat : f.map (Int.castRingHom ℚ)=rationalGap k := by simp [f,gapPoly,rationalGap]
  have sp := split k lo hi
  rw [← rat,map_integer_poly] at sp
  have sep := (GapFamilies.irreducible_gap_rat pos).separable
  change (rationalGap k).Separable at sep
  rw [← rat] at sep
  have mapped := sep.map (f:=algebraMap ℚ K)
  rw [map_integer_poly] at mapped
  have eq := hg f (gap_degree pos).monic mapped sp (low_gap_regular lo (by omega) (reg k lo hi))
  unfold fixed rootType at eq
  rw [rat] at eq
  exact eq.trans (rawRoots_card p k).symm

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- In every common finite Galois splitting field, 127 and 137 give two
elements fixing all four quartic roots, and 17 gives a quartic transposition. -/
theorem three_profiles :
    (∃ u : Aut K, fixedGap K 2 u=0 ∧ fixedGap K 3 u=0 ∧ fixedGap K 4 u=4) ∧
    (∃ v : Aut K, fixedGap K 3 v=1 ∧ fixedGap K 4 v=4) ∧
    (∃ s : Aut K, fixedGap K 4 s=2) := by
  let : Fact (Nat.Prime 127) := ⟨by decide +kernel⟩
  let : Fact (Nat.Prime 137) := ⟨by decide +kernel⟩
  let : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
  obtain ⟨u,hu⟩ := modular_profile K split 127 (by intro k lo hi; interval_cases k <;> decide +kernel)
  obtain ⟨v,hv⟩ := modular_profile K split 137 (by intro k lo hi; interval_cases k <;> decide +kernel)
  obtain ⟨s,hs⟩ := modular_profile K split 17 (by intro k lo hi; interval_cases k <;> decide +kernel)
  refine ⟨⟨u,?_,?_,?_⟩,⟨v,?_,?_⟩,⟨s,?_⟩⟩ <;>
    first | (rw [hu _ (by decide) (by decide)]; decide +kernel)
          | (rw [hv _ (by decide) (by decide)]; decide +kernel)
          | (rw [hs _ (by decide) (by decide)]; decide +kernel)

#print axioms three_profiles
end
end Erdos478.LowGapAction
