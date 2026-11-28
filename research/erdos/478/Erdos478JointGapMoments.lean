import Erdos478GapTuplePatterns
import Erdos478RationalWordOrbits
import Erdos478GapVariance

/-! # Simultaneous mixed moments of factorial gap counts, to degree two in every length -/

namespace Erdos478.GapPatterns
open Polynomial Finset Function BinaryGap RootMoments GapVariance CollisionLaw Filter Topology
open scoped Classical
noncomputable section

private theorem mapped_gap (l : Nat.Primes) : (gap l.val).map (Int.castRingHom ℚ)=rationalGap l.val := by
  simp [gap,rationalGap]

/-- Every first power contributes one and every square contributes two,
even in a product of arbitrarily many different selected lengths. -/
theorem mixed_pair_mean (A : PrimeAverage) {S T : Finset Nat.Primes} (sub : T⊆S)
    (good : ∀ l∈S, broad l.val ∧ 3<l.val) :
    Tendsto (fun X => A.avg X (fun p =>
      (∏ i∈S, observation i p)*(∏ j∈T, observation j p))) atTop (𝓝 (2^(T.card) : ℝ)) := by
  let f (i : S ⊕ T) := gap (lengthAt S T i).val
  let K := AlgebraicClosure ℚ
  have gf (i : S ⊕ T) : Good (f i) := by
    let j := lengthAt S T i
    exact ⟨(gap_degree j).monic,(gap_degree j).natDegree_eq.symm ▸ j.prop.pos,(gap_irr j).separable⟩
  let classified (g : S ⊕ T → ℚ[X]) := ∃ tag : ((i : S ⊕ T) → (g i).rootSet K) → Finset T,
      Surjective tag ∧ ∀ u v, tag u=tag v ↔ ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (u i : K)=v i
  have tags : classified (fun i => (f i).map (Int.castRingHom ℚ)) := by
    have eq : (fun i => (f i).map (Int.castRingHom ℚ))=(fun i => rationalGap (lengthAt S T i).val) :=
      funext fun i => mapped_gap _
    rw [eq]
    exact ⟨label sub,label_onto sub (fun l hl => (good l hl).2),label_orbit sub good⟩
  obtain ⟨tag,onto,orb⟩ := tags
  let : Normal ℚ (AlgebraicClosure ℚ) := normal_fieldOfRoots
  have hm := product_mean_by_labels A f (AlgebraicClosure ℚ) gf (fun _ => IsAlgClosed.splits _) tag onto orb
  have prod (p : ℕ) : (∏ i, roots (f i) p)=(∏ i∈S, observation i p)*(∏ i∈T, observation i p) := by
    rw [Fintype.prod_sum_type]
    change (∏ i : S, observation i.val p)*(∏ i : T, observation i.val p)=_
    exact congrArg₂ (·*·) (prod_coe_sort S (fun i => observation i p)) (prod_coe_sort T (fun i => observation i p))
  simpa only [prod,Fintype.card_finset,Fintype.card_coe,Nat.cast_pow,Nat.cast_ofNat] using hm

#print axioms mixed_pair_mean
end
end Erdos478.GapPatterns
