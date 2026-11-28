import Erdos478CubicGapTransitivity
import Erdos478PairWordSpectrum
import Erdos478WordRootCounts
import Erdos478SeparableRootMean
import Erdos478GapVariance

/-! # Exact second root moment in the two cubic-obstruction classes -/

namespace Erdos478.BinaryGap
open Polynomial Finset Filter Topology RootMoments EffectiveResolvent
open PrimeDifferences CollisionLaw GapVariance
open scoped Polynomial
noncomputable section

theorem square_mean_of_pair_conjugacy (A : PrimeAverage) (l : Nat.Primes)
    (transitive : ∀ {a b c d : (rationalGap l.val).rootSet (rationalGap l.val).SplittingField},
      a≠b → c≠d → ∃ σ : (rationalGap l.val).SplittingField ≃ₐ[ℚ] (rationalGap l.val).SplittingField,
        σ (a:_)=(c:_) ∧ σ (b:_)=(d:_)) :
    Tendsto (fun X => A.avg X (observation l*observation l)) atTop (𝓝 2) := by
  classical
  let f := gap l.val
  let F := rationalGap l.val
  let K := F.SplittingField
  let : Normal ℚ K := SplittingField.instNormal F
  let : NumberField K := ⟨⟩
  have hm : f.Monic := (gap_degree l).monic
  have hdeg : f.natDegree=l.val := (gap_degree l).natDegree_eq
  have lift : f.map (Int.castRingHom ℚ)=F := by simp [f,F,gap,rationalGap]
  have into : F.map (algebraMap ℚ K)=f.map (Int.castRingHom K) := by
    simp [F,f,rationalGap,gap,Polynomial.map_sub,descPochhammer_map]
  have mon : F.Monic := lift ▸ hm.map _
  have sep : F.Separable := (GapFamilies.irreducible_gap_rat l.property.pos).separable
  obtain ⟨v,hv⟩ := enumerate_roots (f.map (Int.castRingHom K)) (hm.map _)
    (into ▸ SplittingField.splits F) (into ▸ sep.map (f:=algebraMap ℚ K))
    ((hm.natDegree_map _).trans hdeg)
  have entry (x : K) : x∈F.rootSet K ↔ ∃ j, x=v j := by
    rw [mon.mem_rootSet,← eval_map_algebraMap,into,hv,eval_prod,Finset.prod_eq_zero_iff]
    simp only [mem_univ,true_and,eval_sub,eval_X,eval_C,sub_eq_zero]
  let r (i : Fin l.val) : F.rootSet K := ⟨v i,(entry _).mpr ⟨i,rfl⟩⟩
  have ri : Function.Injective r := fun _ _ he => v.injective (congrArg Subtype.val he)
  have closed (σ : K ≃ₐ[ℚ] K) (i : Fin l.val) : ∃ j, σ (v i)=v j := by
    apply (entry _).mp
    rw [mon.mem_rootSet,aeval_algHom_apply, (mon.mem_rootSet.mp (r i).property : aeval (v i) F=0),map_zero]
  have conj (i j a b : Fin l.val) (hij : i≠j) (hab : a≠b) :=
    transitive (a:=r i) (b:=r j) (c:=r a) (d:=r b) (ri.ne hij) (ri.ne hab)
  obtain ⟨M,hmon,hpos,hsep,hfac⟩ := pair_word_two f l.property.two_le v hv closed conj
  let W := pairWord f l.val M
  have hw : Tendsto (fun X => A.avg X (RootMoments.roots W)) atTop (𝓝 2) := by
    have H := polynomial_mean A W hmon hsep
    simpa only [factorCount,hfac,Nat.cast_ofNat,W] using H
  let D (P : ℤ[X]) := (P.resultant P.derivative).natAbs
  apply mean_of_change A (b:=RootMoments.roots W) (max (D f) (D W)) _ hw
  intro p hp hpr
  let : Fact p.Prime := ⟨hpr⟩
  have hs := GapFamilies.separable_mod_above_resultant f (hdeg.trans_ne l.property.ne_zero)
    (lift ▸ sep) ((le_max_left ..).trans_lt hp)
  have hW := GapFamilies.separable_mod_above_resultant W hpos.ne' hsep ((le_max_right ..).trans_lt hp)
  have eq := word_root_count (n:=2) (fun _ => f) (fun _ => l.val) (fun _ => hm) (fun _ => hdeg)
    M p (fun _ => hs) hW
  simpa only [Fin.prod_univ_two,Pi.mul_apply,observation,W,pairWord,f] using eq.symm

theorem square_mean (A : PrimeAverage) (l : Nat.Primes) (sel : selected l.val) :
    Tendsto (fun X => A.avg X (observation l*observation l)) atTop (𝓝 2) :=
  square_mean_of_pair_conjugacy A l (root_pair_conjugate l.property sel)

#print axioms square_mean_of_pair_conjugacy
#print axioms square_mean
end
end Erdos478.BinaryGap
