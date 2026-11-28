import Erdos478QuinticJointLaw
import Erdos478QuarticSplittingDegrees

/-! # Exact ordinary-prime coefficients for the first factorial collision at gap five -/

namespace Erdos478.QuinticLaw
open Finset Filter Topology FirstCollision FrobeniusCounts BinaryGap GapDensity GapSieve LowGapAction SplittingDensity
open scoped Classical
noncomputable section

abbrev lengths := insert 5 (short 4)

theorem slots (k : ℕ) : k∈lengths ↔ 2≤k ∧ k≤5 := by
  simp only [lengths,short,mem_insert,mem_Icc]
  omega

def fourBox (a b c f : ℕ → Bool) (n : lengths → ℕ) : Prop :=
  a (n ⟨2,(slots _).mpr (by decide)⟩) && b (n ⟨3,(slots _).mpr (by decide)⟩) &&
  c (n ⟨4,(slots _).mpr (by decide)⟩) && f (n ⟨5,(slots _).mpr (by decide)⟩)

def endpointFourBox (a b c f : ℕ → Bool) (p : ℕ) := fourBox a b c f (fun i => (endpoints i.val p).card)

theorem four_box_density (a b c f : ℕ → Bool) : density lengths (fourBox a b c f)=fourLaw a b c f := by
  let K := FieldOf lengths
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := Polynomial.SplittingField.instNormal _ }
  have law := joint_quintic_law K (fun k lo hi => gap_splits (fun j h => by have := ((slots j).mp h).1; omega)
    ((slots k).mpr ⟨lo,hi⟩)) a b c f
  rw [← law]
  unfold density
  congr 1
  funext g
  unfold fourBox
  split_ifs <;> rfl

theorem endpoint_four_limit (pit : DegreeOnePrimeIdealTheorem) (a b c f : ℕ → Bool) :
    Tendsto (fun X => fraction X (endpointFourBox a b c f)) atTop (𝓝 (fourLaw a b c f)) := by
  rw [← four_box_density]
  exact density_limit pit lengths (fun k hk => ((slots k).mp hk).1) _ _ 0 (fun _ _ _ => Iff.rfl)

private theorem earlier_zero (n : lengths → ℕ) : zeroCounts (earlier 5 (s:=short 4) n) ↔
    (n ⟨2,(slots _).mpr (by decide)⟩=0 ∧ n ⟨3,(slots _).mpr (by decide)⟩=0) ∧
    n ⟨4,(slots _).mpr (by decide)⟩=0 := by
  constructor
  · intro h
    exact ⟨⟨h ⟨2,by decide⟩,h ⟨3,by decide⟩⟩,h ⟨4,by decide⟩⟩
  · rintro ⟨⟨a,b⟩,c⟩ ⟨k,hk⟩
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    rcases (by omega : k=2 ∨ k=3 ∨ k=4) with rfl|rfl|rfl <;> assumption

theorem first_five_density : firstDensity 5=19/288 := by
  let Z (k : ℕ) := k==0
  let P (k : ℕ) := decide (0<k)
  have eq : withHit 5 (s:=short 4) zeroCounts=fourBox Z Z Z P := by
    funext r
    apply propext
    simp only [withHit,earlier_zero,fourBox,Bool.and_eq_true,Z,P,beq_iff_eq,decide_eq_true_eq]
  rw [firstDensity,if_pos (by decide : 2≤5)]
  change density lengths (withHit 5 (s:=short 4) zeroCounts)=_
  rw [eq,four_box_density]
  norm_num [fourLaw,lawValue,binaryWeight,cubicWeight,quarticWeight,quinticWeight,Z,P]

theorem no_five_density : survival 5=11/288 := by
  let Z (k : ℕ) := k==0
  have eq : survival 5=density lengths (fourBox Z Z Z Z) := by
    have len : short 5=lengths := by ext i; rw [slots]; exact mem_Icc
    unfold survival
    rw [len]
    congr 1
    funext n
    apply propext
    simp only [fourBox,Z,Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h; exact ⟨⟨⟨h _,h _⟩,h _⟩,h _⟩
    · rintro ⟨⟨⟨a,b⟩,c⟩,f⟩ ⟨k,hk⟩
      obtain ⟨lo,hi⟩ := (slots k).mp hk
      rcases (by omega : k=2 ∨ k=3 ∨ k=4 ∨ k=5) with rfl|rfl|rfl|rfl <;> assumption
  rw [eq,four_box_density]
  norm_num [fourLaw,lawValue,binaryWeight,cubicWeight,quarticWeight,quinticWeight,Z]

#print axioms lengths
#print axioms slots
#print axioms fourBox
#print axioms endpointFourBox
#print axioms four_box_density
#print axioms endpoint_four_limit
#print axioms first_five_density
#print axioms no_five_density
end
end Erdos478.QuinticLaw
