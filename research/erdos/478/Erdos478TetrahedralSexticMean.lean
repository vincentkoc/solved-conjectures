import Erdos478SexticCountFrequencies
import Erdos478IntegerGapObservables

/-! # The fixed-point mean of any sixth-gap observation in a common splitting field -/

namespace Erdos478.TetrahedralGap
open Finset Filter Topology Polynomial RootMoments CollisionLaw FrobeniusCounts FirstCollision
open SplittingDensity BinaryGap
noncomputable section
open scoped Classical

def sexticMean (v : ℕ → ℝ) : ℝ := (7/12)*v 0+(3/8)*v 2+(1/24)*v 6

theorem sextic_mean (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (sp : ((rationalGap 6).map (algebraMap ℚ K)).Splits) (v : ℕ → ℝ) :
    uniform (Aut K) (fun g => v (fixedGap K 6 g))=sexticMean v := by
  let A := mertensAverage
  let f := gapPoly 6
  let w (r : Unit → ℕ) := v (r ())
  have rat : f.map (Int.castRingHom ℚ)=rationalGap 6 := by simp [f,gapPoly,rationalGap]
  have good : Good f ∧ (f.map (Int.castRingHom K)).Splits := by
    have d := gap_degree (by decide : 0<6)
    refine ⟨⟨d.monic,d.natDegree_eq.symm ▸ (by decide : 0<6),?_⟩,?_⟩
    · rw [rat]
      exact (GapFamilies.irreducible_gap_rat (by decide : 0<6)).separable
    · simpa [f,gapPoly,rationalGap] using sp
  have first := observable_mean A (fun _ : Unit => f) K (fun _ => good) w
  have fixed_eq (g : Aut K) : fixed K f g=fixedGap K 6 g := by
    unfold fixed rootType fixedGap GapRoots
    rw [rat]
  change Tendsto (fun X => A.avg X (fun p => v (primeRoots f p))) atTop
    (𝓝 (uniform (Aut K) (fun g => v (fixed K f g)))) at first
  simp_rw [fixed_eq] at first
  let I (j : ℕ) := event (fun p => (endpoints 6 p).card=j)
  let V := (v 0) • I 0 + (v 2) • I 2 + (v 6) • I 6
  have lim : Tendsto (fun X => A.avg X V) atTop (𝓝 (sexticMean v)) := by
    have h := (((sextic_count_mean A 0).const_mul (v 0)).add
      ((sextic_count_mean A 2).const_mul (v 2))).add ((sextic_count_mean A 6).const_mul (v 6))
    simpa [V,I,map_add,map_smul,smul_eq_mul,sexticMean,sexticFrequency,mul_comm] using h
  apply tendsto_nhds_unique first
  apply mean_of_change A (b:=V) (max 719 (cutoff 6)) _ lim
  intro p hp prime
  have count := ConditionalGaps.endpoint_roots (by decide : 2≤6) prime ((le_max_right ..).trans_lt hp)
  have cases := SexticGap.sextic_endpoints_all_primes prime
  have big : 719<p := (le_max_left ..).trans_lt hp
  rw [if_neg (by omega),if_neg (by omega)] at cases
  change (endpoints 6 p).card=primeRoots f p at count
  rw [← count]
  simp only [V,I,event,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rcases cases with h|h|h <;> simp only [h] <;> norm_num

#print axioms sexticMean
#print axioms sextic_mean
end
end Erdos478.TetrahedralGap
