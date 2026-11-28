import Erdos478ExactFourthAtom
import Erdos478CubicGapIndependence
import Erdos478EvenGapGalois

/-! # Exact degrees of the quartic splitting field and the three-gap compositum -/

namespace Erdos478.LowGapAction
open Finset Polynomial FirstCollision BinaryGap GapReality FrobeniusCounts SplittingDensity
open scoped Classical
noncomputable section

/-- Complete splitting is one element in the 96-element permutation image.
Every finite normal field containing the roots thus has degree divisible by 96. -/
theorem joint_degree_divides (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (split : ∀ k, 2≤k → k≤4 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    96∣Module.finrank ℚ K := by
  let a (n : ℕ) := n==2
  let b (n : ℕ) := n==3
  let c (n : ℕ) := n==4
  let P (g : Aut K) := (a (fixedGap K 2 g) && b (fixedGap K 3 g) && c (fixedGap K 4 g))=true
  let N := (univ.filter P).card
  have eq := joint_fixed_law K split a b c
  have prob : lawValue a b c=1/96 := by norm_num [lawValue,a,b,c,binaryWeight,cubicWeight,quarticWeight]
  have mass : (N:ℝ)/Fintype.card (Aut K)=1/96 := by
    rw [← prob,← eq]
    simp [uniform,N,P,Finset.sum_boole]
  have pos : (Fintype.card (Aut K):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have num : (N:ℝ)*96=Fintype.card (Aut K) := by
    apply (div_eq_div_iff pos (by norm_num)).mp at mass
    simpa using mass
  refine ⟨N,?_⟩
  rw [← IsGalois.card_aut_eq_finrank ℚ K,Nat.card_eq_fintype_card,mul_comm]
  exact_mod_cast num.symm

private theorem individual_bound {k : ℕ} (lo : 2≤k) : Module.finrank ℚ (SplitField (gapPoly k))≤k.factorial := by
  have h := field_degree_bound (by decide : 0<1) {k} (by simpa using (by omega : 0<k))
  simpa [singleton_gap_degree lo] using h

set_option maxHeartbeats 1200000 in
theorem splitting_degrees :
    Module.finrank ℚ (FieldOf lowLengths)=96 ∧ Module.finrank ℚ (SplitField (gapPoly 4))=8 := by
  let K := FieldOf lowLengths
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal _ }
  have slots (i : ℕ) : i∈lowLengths ↔ 2 ≤ i ∧ i ≤ 4 := by
    simp only [lowLengths,short,mem_insert,mem_Icc]
    omega
  have pos (k : ℕ) (hk : k∈lowLengths) : 0<k := by have := ((slots k).mp hk).1; omega
  have dvd := joint_degree_divides K (fun k lo hi => gap_splits pos ((slots k).mpr ⟨lo,hi⟩))
  have lb := Nat.le_of_dvd (Module.finrank_pos (R:=ℚ) (M:=K)) dvd
  let d := Module.finrank ℚ (SplitField (gapPoly 4))
  let w (k : ℕ) := if k=4 then d else k.factorial
  have group := field_degree_bound_of (by decide : 0<1) lowLengths pos w (by
    intro k hk
    by_cases eq : k=4
    · subst k; simp only [w,if_pos rfl,d,le_refl]
    · simpa [w,eq] using individual_bound ((slots k).mp hk).1)
  have small : d≤8 := even_gap_field_degree (r:=2) (by decide)
  have len : lowLengths=({2,3,4} : Finset ℕ) := by decide +kernel
  change Module.finrank ℚ K≤_ at group
  have upper : Nat.totient 1 * ∏ k∈lowLengths, w k=12*d := by
    rw [len]
    norm_num [w,Finset.prod_insert,Nat.factorial]
    ring
  rw [upper] at group
  change Module.finrank ℚ K=96 ∧ d=8
  omega

#print axioms joint_degree_divides
#print axioms splitting_degrees
end
end Erdos478.LowGapAction
