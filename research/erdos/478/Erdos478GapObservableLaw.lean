import Erdos478FairGapDomination
import Erdos478FactorialEndpointCounts
import Erdos478GapSieve

/-! # The finite Galois model for actual factorial collision counts -/

namespace Erdos478.ConditionalGaps
open Polynomial Finset FrobeniusCounts BinaryGap GapVariance RootMoments CollisionLaw
open SplittingDensity Filter Topology
open scoped Classical
noncomputable section

def familyPoly (s : Finset Nat.Primes) := ∏ i∈s, rationalGap i.val
abbrev CommonField (s : Finset Nat.Primes) := (familyPoly s).SplittingField

theorem common_splits {s : Finset Nat.Primes} {i : Nat.Primes} (hi : i∈s) :
    ((rationalGap i.val).map (algebraMap ℚ (CommonField s))).Splits := by
  let F := familyPoly s
  have mon : F.Monic := monic_prod_of_monic _ _ (fun j _ => by
    have h := (GapVariance.gap_degree j).monic.map (Int.castRingHom ℚ)
    simpa [gap,rationalGap] using h)
  exact (SplittingField.splits F).of_dvd (mon.map _).ne_zero
    (Polynomial.map_dvd _ (dvd_prod_of_mem (fun j : Nat.Primes => rationalGap j.val) hi))

/-- The polynomial root count agrees with actual factorial endpoints for every integer length at least two. -/
theorem endpoint_roots {k : ℕ} (hk : 2≤k) {p : ℕ} (hp : p.Prime) (hc : cutoff k<p) :
    (endpoints k p).card=primeRoots (gap k) p := by
  have hkpos : 0<k := by omega
  let : Fact p.Prime := ⟨hp⟩
  have deg := SplittingDensity.gap_degree hkpos
  have sep := GapFamilies.separable_mod_above_resultant (gapPoly k) (deg.natDegree_eq.trans_ne hkpos.ne')
    (by simpa [gapPoly] using (GapFamilies.irreducible_gap_rat hkpos).separable) ((le_max_right ..).trans_lt hc)
  apply (Nat.cast_inj (R:=ℝ)).mp
  change ((endpoints k p).card : ℝ)=RootMoments.roots (gapPoly k) p
  rw [endpoint_count hk hc,count_roots _ deg.monic p sep]

/-- For a fixed finite family, every statistic of the actual numbers of
factorial endpoint collisions has its ordinary Galois fixed-point model. -/
theorem endpoint_mean (A : PrimeAverage) (s : Finset Nat.Primes) (w : (s → ℕ) → ℝ) :
    Tendsto (fun X => A.avg X (fun p => w (fun i => (endpoints i.val.val p).card))) atTop
      (𝓝 (uniform (Aut (CommonField s)) (fun g => w (fun i => count (CommonField s) i.val g)))) := by
  let K := CommonField s
  let : Normal ℚ K := SplittingField.instNormal (familyPoly s)
  have hf (i : s) : Good (gap i.val.val) ∧ ((gap i.val.val).map (Int.castRingHom K)).Splits := by
    have d := GapVariance.gap_degree i.val
    refine ⟨⟨d.monic,d.natDegree_eq.symm ▸ i.val.prop.pos,(gap_irr i.val).separable⟩,?_⟩
    simpa [gap,rationalGap] using common_splits i.prop
  have h := observable_mean A (fun i : s => gap i.val.val) K hf w
  simp_rw [count_eq]
  apply mean_of_change A (b:=fun p => w (fun i => primeRoots (gap i.val.val) p)) (s.sup (fun i => cutoff i.val)) _ h
  intro p hp hpr
  apply congrArg w
  funext i
  exact endpoint_roots i.val.prop.two_le hpr ((le_sup i.prop).trans_lt hp)

theorem hasGap_iff {p k : ℕ} : GapSieve.HasGap p k ↔ 0<(endpoints k p).card := by
  rw [card_pos]
  constructor
  · rintro ⟨j,hj,hk,eq⟩
    exact ⟨j+k,mem_filter.mpr ⟨mem_Ico.mpr ⟨by have := (mem_Ico.mp hj).1; omega,(mem_Ico.mp hk).2⟩,
      by simpa using eq⟩⟩
  · rintro ⟨j,hj⟩
    obtain ⟨h,eq⟩ := mem_filter.mp hj
    obtain ⟨lo,hi⟩ := mem_Ico.mp h
    have e : j-k+k=j := by omega
    exact ⟨j-k,mem_Ico.mpr ⟨by omega,by omega⟩,by rw [e]; exact mem_Ico.mpr ⟨by omega,hi⟩,by simpa only [e] using eq⟩

private def select (s : Finset Nat.Primes) (a : s → ℕ) := s.attach.filter (fun i => 0<a i) |>.map (Function.Embedding.subtype _)

theorem hit_score_mean (A : PrimeAverage) (s : Finset Nat.Primes) (f : Finset Nat.Primes → ℝ) :
    Tendsto (fun X => A.avg X (fun p => f (GapSieve.hits s p))) atTop
      (𝓝 (uniform (Aut (CommonField s)) (fun g => f (hits (CommonField s) s g)))) := by
  classical
  have ps (p : ℕ) : select s (fun i => (endpoints i.val.val p).card)=GapSieve.hits s p := by
    ext i
    simp [select,GapSieve.hits,hasGap_iff,and_comm]
  have gs (g : Aut (CommonField s)) : select s (fun i => count (CommonField s) i.val g)=hits (CommonField s) s g := by
    ext i
    simp [select,hits,and_comm]
  simpa only [Function.comp_apply,ps,gs] using endpoint_mean A s (f ∘ select s)

#print axioms familyPoly
#print axioms CommonField
#print axioms common_splits
#print axioms endpoint_roots
#print axioms endpoint_mean
#print axioms hasGap_iff
#print axioms hit_score_mean
end
end Erdos478.ConditionalGaps
