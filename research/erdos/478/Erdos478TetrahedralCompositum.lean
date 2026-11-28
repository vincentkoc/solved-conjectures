import Erdos478SixthCollisionAtom
import Erdos478QuinticSplittingDegrees

/-! # Exact degree of the composite field for factorial gaps two through six -/

namespace Erdos478.TetrahedralGap
open Finset Polynomial FirstCollision BinaryGap GapReality FrobeniusCounts SplittingDensity LowGapAction QuinticLaw
open scoped Classical
noncomputable section

theorem sextic_product_action (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤6 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    Function.Surjective ((lowerAction K (short 5)).rangeRestrict.prod (vertexAction K)) :=
  RelativeGap.range_product _ _ (vertex_relative_surjective K split)

theorem five_degree_divides (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤6 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    276480∣Module.finrank ℚ K := by
  let P (g : Aut K) := (fixedGap K 2 g==2 && fixedGap K 3 g==3 && fixedGap K 4 g==4 &&
    fixedGap K 5 g==5 && fixedGap K 6 g==6)=true
  let N := (univ.filter P).card
  have eq := joint_sextic_law K split (·==2) (·==3) (·==4) (·==5) (·==6)
  have prob : fiveLaw (·==2) (·==3) (·==4) (·==5) (·==6)=1/276480 := by
    norm_num [fiveLaw,fourLaw,sexticMean,lawValue,binaryWeight,cubicWeight,quarticWeight,quinticWeight]
  have mass : (N:ℝ)/Fintype.card (Aut K)=1/276480 := by
    rw [← prob,← eq]
    simp [uniform,N,P,Finset.sum_boole]
  have num := (div_eq_div_iff (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α:=Aut K))) (by norm_num)).mp mass
  refine ⟨N,?_⟩
  rw [← IsGalois.card_aut_eq_finrank ℚ K,Nat.card_eq_fintype_card,mul_comm]
  exact_mod_cast (show (N:ℝ)*276480=Fintype.card (Aut K) by simpa using num).symm

theorem five_compositum_degree : Module.finrank ℚ (FieldOf sixLengths)=276480 := by
  let K := FieldOf sixLengths
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal _ }
  have pos (k : ℕ) (h : k∈sixLengths) : 0<k := by have := ((six_slots k).mp h).1; omega
  have dvd := five_degree_divides K (fun k lo hi => gap_splits pos ((six_slots k).mpr ⟨lo,hi⟩))
  apply Nat.le_antisymm _ (Nat.le_of_dvd (Module.finrank_pos (R:=ℚ) (M:=K)) dvd)
  let w (k : ℕ) := if k=4 then 8 else if k=5 then 120 else if k=6 then 24 else k.factorial
  have bound := field_degree_bound_of (by decide : 0<1) sixLengths pos w (by
    intro k hk
    by_cases h₄ : k=4
    · subst k; simpa [w] using LowGapAction.splitting_degrees.2.le
    by_cases h₅ : k=5
    · subst k; simpa [w] using quintic_degrees.2.le
    by_cases h₆ : k=6
    · subst k; simpa [w] using SexticGap.sextic_splitting_degree.le
    have old := field_degree_bound (by decide : 0<1) {k} (by simpa using pos k hk)
    simpa [w,h₄,h₅,h₆,singleton_gap_degree ((six_slots k).mp hk).1] using old)
  have len : sixLengths=({2,3,4,5,6} : Finset ℕ) := by decide +kernel
  have val : Nat.totient 1*∏ k∈sixLengths,w k=276480 := by rw [len]; norm_num [w,Finset.prod_insert,Nat.factorial]
  exact bound.trans_eq val

#print axioms sextic_product_action
#print axioms five_degree_divides
#print axioms five_compositum_degree
end
end Erdos478.TetrahedralGap
