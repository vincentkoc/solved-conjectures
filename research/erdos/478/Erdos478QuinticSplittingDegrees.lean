import Erdos478FifthCollisionAtom

/-! # The quintic splitting field and the compositum of factorial gaps two through five -/

namespace Erdos478.QuinticLaw
open Finset Polynomial FirstCollision BinaryGap GapReality FrobeniusCounts SplittingDensity LowGapAction
open scoped Classical
noncomputable section

/-- Every lower root permutation tuple that occurs can be combined with every
permutation of the five roots, in the same field automorphism. -/
theorem quintic_product_action (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤5 → ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (e : GapRoots K 5 ≃ Fin 5) : Function.Surjective
      ((lowerAction K (short 4)).rangeRestrict.prod (numberedAction K e)) :=
  RelativeGap.range_product _ _ (quintic_relative_surjective K split e)

theorem four_degree_divides (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤5 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    11520∣Module.finrank ℚ K := by
  let a (n : ℕ) := n==2
  let b (n : ℕ) := n==3
  let c (n : ℕ) := n==4
  let f (n : ℕ) := n==5
  let P (g : Aut K) := (a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g) && f (fixedGap K 5 g))=true
  let N := (univ.filter P).card
  have eq := joint_quintic_law K split a b c f
  have prob : fourLaw a b c f=1/11520 := by
    norm_num [fourLaw,lawValue,a,b,c,f,binaryWeight,cubicWeight,quarticWeight,quinticWeight]
  have mass : (N:ℝ)/Fintype.card (Aut K)=1/11520 := by
    rw [← prob,← eq]
    simp [uniform,N,P,Finset.sum_boole]
  have pos : (Fintype.card (Aut K):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have num := (div_eq_div_iff pos (by norm_num)).mp mass
  refine ⟨N,?_⟩
  rw [← IsGalois.card_aut_eq_finrank ℚ K,Nat.card_eq_fintype_card,mul_comm]
  exact_mod_cast (show (N:ℝ)*11520=Fintype.card (Aut K) by simpa using num).symm

private theorem single_bound {k : ℕ} (lo : 2≤k) : Module.finrank ℚ (SplitField (gapPoly k))≤k.factorial := by
  have h := field_degree_bound (by decide : 0<1) {k} (by simpa using (by omega : 0<k))
  simpa [singleton_gap_degree lo] using h

set_option maxHeartbeats 1200000 in
theorem quintic_degrees :
    Module.finrank ℚ (FieldOf lengths)=11520 ∧ Module.finrank ℚ (SplitField (gapPoly 5))=120 := by
  let K := FieldOf lengths
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal _ }
  have pos (k : ℕ) (h : k∈lengths) : 0<k := by have := ((slots k).mp h).1; omega
  have dvd := four_degree_divides K (fun k lo hi => gap_splits pos ((slots k).mpr ⟨lo,hi⟩))
  have lb := Nat.le_of_dvd (Module.finrank_pos (R:=ℚ) (M:=K)) dvd
  let d := Module.finrank ℚ (SplitField (gapPoly 5))
  let w (k : ℕ) := if k=4 then 8 else if k=5 then d else k.factorial
  have bound := field_degree_bound_of (by decide : 0<1) lengths pos w (by
    intro k hk
    by_cases h₄ : k=4
    · subst k; simpa [w] using LowGapAction.splitting_degrees.2.le
    by_cases h₅ : k=5
    · subst k; simp [w,d]
    simpa [w,h₄,h₅] using single_bound ((slots k).mp hk).1)
  have small : d≤120 := single_bound (by decide : 2≤5)
  have len : lengths=({2,3,4,5} : Finset ℕ) := by decide +kernel
  change Module.finrank ℚ K≤_ at bound
  have upper : Nat.totient 1 * ∏ k∈lengths,w k=96*d := by
    rw [len]
    norm_num [w,Finset.prod_insert,Nat.factorial]
    ring
  rw [upper] at bound
  change Module.finrank ℚ K=11520 ∧ d=120
  omega

#print axioms quintic_product_action
#print axioms four_degree_divides
#print axioms quintic_degrees
end
end Erdos478.QuinticLaw
