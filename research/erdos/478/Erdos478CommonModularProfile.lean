import Erdos478SimultaneousModularWitness
import Erdos478IntegerGapObservables

/-! # A common modular root profile in any finite Galois field splitting the chosen gaps -/

namespace Erdos478.RelativeGap
open Polynomial Finset LocalWitness SplittingDensity FrobeniusCounts FirstCollision BinaryGap RootMoments
noncomputable section

theorem regular_profile (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (s : Finset ℕ) (pos : ∀ k∈s, 0<k)
    (split : ∀ k∈s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (p : ℕ) [Fact p.Prime] (regular : ∀ k∈s, ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable) :
    ∃ g : Aut K, ∀ k∈s, fixedGap K k g=primeRoots (gapPoly k) p := by
  obtain ⟨g,hg⟩ := simultaneous_witness K p
  refine ⟨g,fun k hk => ?_⟩
  let f := gapPoly k
  have rat : f.map (Int.castRingHom ℚ)=rationalGap k := by simp [f,gapPoly,rationalGap]
  have sp := split k hk
  rw [← rat,map_integer_poly] at sp
  have sep := (GapFamilies.irreducible_gap_rat (pos k hk)).separable
  change (rationalGap k).Separable at sep
  rw [← rat] at sep
  have mapped := sep.map (f:=algebraMap ℚ K)
  rw [map_integer_poly] at mapped
  have eq := hg f (gap_degree (pos k hk)).monic mapped sp (regular k hk)
  unfold fixed rootType at eq
  rwa [rat] at eq

#print axioms regular_profile
end
end Erdos478.RelativeGap
