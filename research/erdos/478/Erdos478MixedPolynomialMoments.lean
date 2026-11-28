import Erdos478WordRootCounts
import Erdos478SeparableRootMean

/-!
# Mixed moments for any tuple of separable integral polynomials

Repeated inputs give ordinary powers of their root counts. The moment is the
number of rational factors of the word polynomial at its least separating
nonnegative integer weight.
-/

namespace Erdos478.CollisionLaw
noncomputable section
open Polynomial Finset Filter Topology EffectiveResolvent RootMoments

def Good (f : ℤ[X]) := f.Monic ∧ 0<f.natDegree ∧ (f.map (Int.castRingHom ℚ)).Separable

def wordAt (fs : List ℤ[X]) (M : ℕ) :=
  wordPolynomial fs.length fs.get (fun i => (fs.get i).natDegree) (M:ℤ)

def weight (fs : List ℤ[X]) := sInf {M : ℕ | Good (wordAt fs M)}

def moment (fs : List ℤ[X]) := factorCount (wordAt fs (weight fs))

def productRoots (fs : List ℤ[X]) (p : ℕ) := (fs.map fun f => RootMoments.roots f p).prod

theorem good_at_weight (fs : List ℤ[X]) (good : ∀ f∈fs, Good f) : Good (wordAt fs (weight fs)) := by
  classical
  apply Nat.sInf_mem (s:={M : ℕ | Good (wordAt fs M)})
  let d (i : Fin fs.length) := (fs.get i).natDegree
  have H (i : Fin fs.length) := good _ (List.get_mem fs i)
  have lift (P : ℤ[X]) : (P.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)=P.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map,RingHom.ext_int ((algebraMap ℚ ℂ).comp _) (Int.castRingHom ℂ)]
  choose a ha using fun i => enumerate_roots ((fs.get i).map (Int.castRingHom ℂ))
    ((H i).1.map _) (IsAlgClosed.splits _) (lift _ ▸ (H i).2.2.map (f:=algebraMap ℚ ℂ)) ((H i).1.natDegree_map _)
  have sep : ∃ M : ℕ, Function.Injective (fun t : Word d => wordValue (M:ℂ) (fun i => a i (t i))) := by
    by_cases hn : 0<fs.length
    · obtain ⟨M,_,hM⟩ := word_separator hn d a
      exact ⟨M,hM⟩
    · refine ⟨0,fun u v _ => funext fun i => ?_⟩
      have := i.isLt
      omega
  obtain ⟨M,hM⟩ := sep
  let val (t : Word d) := wordValue (M:ℂ) (fun i => a i (t i))
  have hw : (wordAt fs M).map (Int.castRingHom ℂ)=∏ t : Word d, (X-C (val t)) := by
    unfold wordAt
    rw [wordPolynomial_map]
    simp_rw [ha]
    simpa only [val,Nat.cast_ofNat,Int.coe_castRingHom,Int.cast_natCast] using
      wordPolynomial_factors d (fun i => a i) (M:ℂ)
  have hm : (wordAt fs M).Monic := (Function.Injective.monic_map_iff (f:=Int.castRingHom ℂ)
    (by exact Int.cast_injective)).mpr (hw ▸ monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  let : Nonempty (Word d) := ⟨fun i => ⟨0,(H i).2.1⟩⟩
  refine ⟨M,hm,?_,?_⟩
  · rw [← hm.natDegree_map (Int.castRingHom ℂ),hw]
    simpa using (Fintype.card_pos (α:=Word d))
  · apply (separable_map (algebraMap ℚ ℂ)).mp
    rw [lift,hw]
    exact separable_prod_X_sub_C_iff.mpr hM

/-- Mixed moments exist without pairwise-coprime degrees or disjoint fields. -/
theorem mixed_root_mean (A : PrimeAverage) (fs : List ℤ[X]) (good : ∀ f∈fs, Good f) :
    Tendsto (fun X => A.avg X (productRoots fs)) atTop (𝓝 (moment fs : ℝ)) := by
  classical
  let W := wordAt fs (weight fs)
  have hW : Good W := good_at_weight fs good
  let D (f : ℤ[X]) := (f.resultant f.derivative).natAbs
  let B := univ.sup (fun i : Fin fs.length => D (fs.get i))
  apply mean_of_change A (b:=RootMoments.roots W) (max (D W) B) _ (polynomial_mean A W hW.1 hW.2.2)
  intro p hp hpr
  let : Fact p.Prime := ⟨hpr⟩
  have H (i : Fin fs.length) := good _ (List.get_mem fs i)
  have h := word_root_count fs.get (fun i => (fs.get i).natDegree) (fun i => (H i).1) (fun _ => rfl)
    (weight fs) p (fun i => GapFamilies.separable_mod_above_resultant _ (H i).2.1.ne' (H i).2.2
      (lt_of_le_of_lt (le_sup (f:=fun i : Fin fs.length => D (fs.get i)) (mem_univ i)) ((le_max_right ..).trans_lt hp)))
    (GapFamilies.separable_mod_above_resultant W hW.2.1.ne' hW.2.2 ((le_max_left ..).trans_lt hp))
  refine Eq.trans ?_ h.symm
  change (fs.map _).prod=_
  rw [← List.prod_ofFn]
  exact congrArg List.prod (by simpa [Function.comp_def] using (List.map_ofFn (g:=fun f => RootMoments.roots f p) (f:=fs.get)))

#print axioms good_at_weight
#print axioms mixed_root_mean
end
end Erdos478.CollisionLaw
