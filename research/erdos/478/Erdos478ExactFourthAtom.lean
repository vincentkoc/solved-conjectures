import Erdos478QuarticJointAction
import Erdos478LeastPrimeCollision

/-! # Exact density of the first factorial collision at distance four -/

namespace Erdos478.LowGapAction
open Finset Filter Topology FirstCollision FrobeniusCounts BinaryGap GapDensity GapSieve SplittingDensity
open scoped Classical
noncomputable section

abbrev lowLengths := insert 4 (short 3)
private theorem slots (k : ℕ) : k∈lowLengths ↔ 2≤k ∧ k≤4 := by
  simp only [lowLengths,short,mem_insert,mem_Icc]
  omega

def lowBox (a b c : ℕ → Bool) (n : lowLengths → ℕ) : Prop :=
  a (n ⟨2,(slots 2).mpr (by decide)⟩) && b (n ⟨3,(slots 3).mpr (by decide)⟩) &&
    c (n ⟨4,(slots 4).mpr (by decide)⟩)

def endpointBox (a b c : ℕ → Bool) (p : ℕ) := lowBox a b c (fun i => (endpoints i.val p).card)

theorem low_box_density (a b c : ℕ → Bool) : density lowLengths (lowBox a b c)=lawValue a b c := by
  let K := FieldOf lowLengths
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := Polynomial.SplittingField.instNormal _ }
  have law := joint_fixed_law K (fun k lo hi => gap_splits (fun j hj => by have := ((slots j).mp hj).1; omega)
    ((slots k).mpr ⟨lo,hi⟩)) a b c
  rw [← law]
  unfold density
  congr 1
  funext g
  unfold lowBox
  split_ifs <;> rfl

theorem endpoint_box_limit (pit : DegreeOnePrimeIdealTheorem) (a b c : ℕ → Bool) :
    Tendsto (fun X => fraction X (endpointBox a b c)) atTop (𝓝 (lawValue a b c)) := by
  rw [← low_box_density]
  exact density_limit pit lowLengths (fun k hk => ((slots k).mp hk).1) _ _ 0 (fun _ _ _ => Iff.rfl)

private theorem earlier_zero (n : lowLengths → ℕ) : zeroCounts (earlier 4 (s:=short 3) n) ↔
    n ⟨2,(slots 2).mpr (by decide)⟩=0 ∧ n ⟨3,(slots 3).mpr (by decide)⟩=0 := by
  constructor
  · intro h
    exact ⟨h ⟨2,by decide⟩,h ⟨3,by decide⟩⟩
  · rintro ⟨h₂,h₃⟩ ⟨i,hi⟩
    have bounds : 2 ≤ i ∧ i ≤ 3 := mem_Icc.mp hi
    obtain ⟨lo,up⟩ := bounds
    rcases (by omega : i=2 ∨ i=3) with rfl|rfl
    · exact h₂
    · exact h₃

theorem first_four_density : firstDensity 4=1/16 := by
  let Z (n : ℕ) := n==0
  let P (n : ℕ) := decide (0<n)
  have event : withHit 4 (s:=short 3) zeroCounts=lowBox Z Z P := by
    funext n
    apply propext
    simp only [withHit,earlier_zero,lowBox,Bool.and_eq_true,Z,P,beq_iff_eq,decide_eq_true_eq]
  rw [firstDensity,if_pos (by decide : 2≤4)]
  change density lowLengths (withHit 4 (s:=short 3) zeroCounts)=_
  rw [event,low_box_density]
  norm_num [lawValue,binaryWeight,cubicWeight,quarticWeight,Z,P]

theorem no_four_density : survival 4=5/48 := by
  let Z (n : ℕ) := n==0
  have eq : survival 4=density lowLengths (lowBox Z Z Z) := by
    have len : short 4=lowLengths := by ext i; rw [slots]; exact mem_Icc
    unfold survival
    rw [len]
    congr 1
    funext n
    apply propext
    simp only [lowBox,Z,Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h; exact ⟨⟨h _,h _⟩,h _⟩
    · rintro ⟨⟨a,b⟩,c⟩ ⟨i,hi⟩
      obtain ⟨lo,up⟩ := (slots i).mp hi
      rcases (by omega : i=2 ∨ i=3 ∨ i=4) with rfl|rfl|rfl
      · exact a
      · exact b
      · exact c
  rw [eq,low_box_density]
  norm_num [lawValue,binaryWeight,cubicWeight,quarticWeight,Z]

#print axioms lowLengths
#print axioms lowBox
#print axioms endpointBox
#print axioms low_box_density
#print axioms endpoint_box_limit
#print axioms first_four_density
#print axioms no_four_density
end
end Erdos478.LowGapAction
