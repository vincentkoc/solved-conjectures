import Erdos478GaloisFixedMoments
import Erdos478JointCountInterpolation

/-! # Prime densities of joint root-count events in a common normal field -/

namespace Erdos478.FrobeniusCounts
open Polynomial CollisionLaw RootMoments Filter Topology
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [Normal ℚ K]

private def fixedShift (qs : List (ℤ[X] × ℕ)) (g : Aut K) : ℝ :=
  (qs.map fun q => (fixed K q.1 g : ℝ)-q.2).prod

private theorem shift_eq_uniform (qs : List (ℤ[X] × ℕ)) (fs : List ℤ[X])
    (hs : ∀ f∈fs, Good f ∧ (f.map (Int.castRingHom K)).Splits)
    (hq : ∀ q∈qs, Good q.1 ∧ (q.1.map (Int.castRingHom K)).Splits) :
    (shiftedMoment fs qs : ℝ)=uniform (Aut K) (fun g => fixedProduct K fs g*fixedShift K qs g) := by
  induction qs generalizing fs with
  | nil =>
    simpa [shiftedMoment,fixedShift] using moment_eq_uniform K fs (fun f h => (hs f h).1) (fun f h => (hs f h).2)
  | cons q qs ih =>
    rcases q with ⟨f,j⟩
    have ht := fun u (hu:u∈qs) => hq u (List.mem_cons_of_mem _ hu)
    have hf := ih (f::fs) (by simpa using And.intro (hq _ List.mem_cons_self) hs) ht
    rw [shiftedMoment,Int.cast_sub,Int.cast_mul,Int.cast_natCast,hf,ih fs hs ht]
    let u := fun g => fixedProduct K (f::fs) g*fixedShift K qs g
    let v := fun g => fixedProduct K fs g*fixedShift K qs g
    change uniform (Aut K) u-(j:ℝ)*uniform (Aut K) v=_
    rw [← smul_eq_mul,← map_smul,← map_sub]
    apply congrArg (uniform (Aut K))
    funext g
    simp [u,v,fixedProduct,fixedShift]
    ring

/-- Exact root counts of a uniform Galois automorphism. -/
def hasFixedCounts (ts : List Test) (g : Aut K) := ∀ t∈ts, fixed K t.poly g=t.count

/-- The rational density from interpolation equals the proportion of group
elements with the prescribed counts, allowing overlapping splitting fields. -/
theorem joint_density_eq_uniform (ts : List Test)
    (hg : ∀ t∈ts, Good t.poly ∧ (t.poly.map (Int.castRingHom K)).Splits) :
    (jointDensity ts : ℝ)=uniform (Aut K) (fun g => if hasFixedCounts K ts g then 1 else 0) := by
  classical
  let D : ℝ := denominator ts
  have hd : D≠0 := by dsimp [D]; exact_mod_cast denominator_ne_zero ts
  let v (g : Aut K) : ℝ := if hasFixedCounts K ts g then 1 else 0
  have he : fixedShift K (shifts ts) = D • v := by
    funext g
    have h := interpolation_at (fun f => (fixed K f g : ℝ)) ts
      (fun t _ => ⟨_,fixed_le_degree K t.poly g,rfl⟩)
    unfold fixedShift
    have cond : (∀ t∈ts, (fixed K t.poly g : ℝ)=(t.count : ℝ)) ↔ hasFixedCounts K ts g := by
      simp only [Nat.cast_inj,hasFixedCounts]
    rw [h]
    by_cases yes : hasFixedCounts K ts g
    · rw [if_pos (cond.mpr yes)]
      simp [v,yes,D]
    · rw [if_neg (fun hh => yes (cond.mp hh))]
      simp [v,yes]
  have lim := shift_eq_uniform K (shifts ts) [] (by simp) (by
    intro q hq
    obtain ⟨t,ht,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact hg t ht)
  simp only [fixedProduct,List.map_nil,List.prod_nil,one_mul,he, map_smul,smul_eq_mul] at lim
  change (jointDensity ts : ℝ)=uniform (Aut K) v
  simp only [jointDensity,Rat.cast_div,Rat.cast_intCast]
  apply (div_eq_iff hd).mpr
  simpa [mul_comm] using lim

/-- Joint prime law for bounded fixed-point observations, at every prime
average satisfying the degree-one mean theorem. -/
theorem joint_fixed_mean (A : PrimeAverage) (ts : List Test)
    (hg : ∀ t∈ts, Good t.poly ∧ (t.poly.map (Int.castRingHom K)).Splits) :
    Tendsto (fun X => A.avg X (SplittingDensity.event (hasCounts ts))) atTop
      (𝓝 (uniform (Aut K) (fun g => if hasFixedCounts K ts g then 1 else 0))) := by
  rw [← joint_density_eq_uniform K ts hg]
  exact CollisionLaw.joint_mean A ts (fun t ht => (hg t ht).1)

#print axioms hasFixedCounts
#print axioms joint_density_eq_uniform
#print axioms joint_fixed_mean
end
end Erdos478.FrobeniusCounts
