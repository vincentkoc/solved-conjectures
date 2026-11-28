import Erdos478GaloisCountLaw

/-! # Joint prime laws for arbitrary functions of finitely many root counts -/

namespace Erdos478.FrobeniusCounts
open Finset Polynomial RootMoments CollisionLaw Filter Topology
open scoped Classical
noncomputable section

def primeRoots (f : ℤ[X]) (p : ℕ) := Nat.card (RootPairs.solutions f (ZMod p))

theorem primeRoots_le {f : ℤ[X]} (hm : f.Monic) {p : ℕ} (hp : p.Prime) :
    primeRoots f p≤f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  let e : RootPairs.solutions f (ZMod p) ≃ F.roots.toFinset :=
    Equiv.subtypeEquivRight fun x => by simp [F,mem_roots (hm.map _).ne_zero,IsRoot,eval_map]
  change Nat.card _≤_
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
  exact (Multiset.toFinset_card_le F.roots).trans ((card_roots' F).trans (hm.natDegree_map _).le)

variable {I : Type*} [Fintype I]
abbrev Counts (f : I → ℤ[X]) := (i : I) → Fin ((f i).natDegree+1)

private def tests (f : I → ℤ[X]) (a : Counts f) : List Test :=
  (univ : Finset I).toList.map fun i => ⟨f i,(a i).val⟩

private theorem expand (f : I → ℤ[X]) (w : (I → ℕ) → ℝ) (x : I → ℕ) (hx : ∀ i, x i≤(f i).natDegree) :
    (∑ a : Counts f, w (fun i => a i)*(if ∀ i, x i=(a i).val then 1 else 0))=w x := by
  classical
  let a : Counts f := fun i => ⟨x i,Nat.lt_succ_of_le (hx i)⟩
  rw [sum_eq_single a]
  · simp [a]
  · intro b _ hb
    have h : ¬ ∀ i, x i=(b i).val := fun he => hb (funext fun i => Fin.ext (he i).symm)
    simp [h]
  · simp

/-- Every function of a finite family of prime root counts has the same
limiting mean as its fixed-point analogue in any common finite normal
splitting field. No regularity is needed on the observation function. -/
theorem observable_mean (A : PrimeAverage) (f : I → ℤ[X]) (K : Type*) [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [Normal ℚ K] (hf : ∀ i, Good (f i) ∧ ((f i).map (Int.castRingHom K)).Splits)
    (w : (I → ℕ) → ℝ) :
    Tendsto (fun X => A.avg X (fun p => w (fun i => primeRoots (f i) p))) atTop
      (𝓝 (uniform (Aut K) (fun g => w (fun i => fixed K (f i) g)))) := by
  classical
  let v (a : Counts f) : ℝ := w (fun i => a i)
  let P (a : Counts f) := SplittingDensity.event (hasCounts (tests f a))
  let Q (a : Counts f) (g : Aut K) : ℝ := if hasFixedCounts K (tests f a) g then 1 else 0
  have atoms (a : Counts f) := joint_fixed_mean K A (tests f a) (by
    intro t ht
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    exact hf i)
  have lim := tendsto_finsetSum (univ : Finset (Counts f)) fun a _ => (atoms a).const_mul (v a)
  have group : (∑ a : Counts f, v a • Q a)=(fun g => w (fun i => fixed K (f i) g)) := by
    funext g
    have cond (a : Counts f) : hasFixedCounts K (tests f a) g ↔ ∀ i, fixed K (f i) g=(a i).val := by
      simp [hasFixedCounts,tests]
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Q,cond,v] using
      expand f w (fun i => fixed K (f i) g) (fun i => fixed_le_degree K (f i) g)
  apply mean_of_change A (b:=∑ a : Counts f, v a • P a) 0
  · intro p _ hp
    have cond (a : Counts f) : hasCounts (tests f a) p ↔ ∀ i, primeRoots (f i) p=(a i).val := by
      simp [hasCounts,tests,RootMoments.roots,primeRoots]
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,P,SplittingDensity.event,cond,v] using
      (expand f w (fun i => primeRoots (f i) p) (fun i => primeRoots_le (hf i).1.1 hp)).symm
  · rw [← group]
    simpa only [map_sum,map_smul,smul_eq_mul,P,Q] using lim

#print axioms primeRoots
#print axioms primeRoots_le
#print axioms Counts
#print axioms observable_mean
end
end Erdos478.FrobeniusCounts
