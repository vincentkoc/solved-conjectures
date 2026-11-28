import Erdos478TetrahedralJointLaw
import Erdos478FifthCollisionAtom

/-! # First collision at distance six and survival through six -/

namespace Erdos478.TetrahedralGap
open Finset Filter Topology FirstCollision FrobeniusCounts BinaryGap GapDensity GapSieve LowGapAction SplittingDensity QuinticLaw
open scoped Classical
noncomputable section

abbrev sixLengths := insert 6 (short 5)

theorem six_slots (k : ℕ) : k∈sixLengths ↔ 2≤k ∧ k≤6 := by
  simp only [sixLengths,short,mem_insert,mem_Icc]
  omega

def fiveBox (a b c d e : ℕ → Bool) (n : sixLengths → ℕ) : Prop :=
  a (n ⟨2,(six_slots _).mpr (by decide)⟩) && b (n ⟨3,(six_slots _).mpr (by decide)⟩) &&
  c (n ⟨4,(six_slots _).mpr (by decide)⟩) && d (n ⟨5,(six_slots _).mpr (by decide)⟩) &&
  e (n ⟨6,(six_slots _).mpr (by decide)⟩)

def endpointFiveBox (a b c d e : ℕ → Bool) (p : ℕ) := fiveBox a b c d e (fun i => (endpoints i.val p).card)

theorem five_box_density (a b c d e : ℕ → Bool) : density sixLengths (fiveBox a b c d e)=fiveLaw a b c d e := by
  let K := FieldOf sixLengths
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := Polynomial.SplittingField.instNormal _ }
  have law := joint_sextic_law K (fun k lo hi => gap_splits (fun j h => by have := ((six_slots j).mp h).1; omega)
    ((six_slots k).mpr ⟨lo,hi⟩)) a b c d e
  rw [← law]
  unfold density
  congr 1
  funext g
  unfold fiveBox
  split_ifs <;> rfl

theorem endpoint_five_limit (pit : DegreeOnePrimeIdealTheorem) (a b c d e : ℕ → Bool) :
    Tendsto (fun X => fraction X (endpointFiveBox a b c d e)) atTop (𝓝 (fiveLaw a b c d e)) := by
  rw [← five_box_density]
  exact density_limit pit sixLengths (fun k hk => ((six_slots k).mp hk).1) _ _ 0 (fun _ _ _ => Iff.rfl)

private theorem earlier_zero (n : sixLengths → ℕ) : zeroCounts (earlier 6 (s:=short 5) n) ↔
    ((n ⟨2,(six_slots _).mpr (by decide)⟩=0 ∧ n ⟨3,(six_slots _).mpr (by decide)⟩=0) ∧
    n ⟨4,(six_slots _).mpr (by decide)⟩=0) ∧ n ⟨5,(six_slots _).mpr (by decide)⟩=0 := by
  constructor
  · intro h
    exact ⟨⟨⟨h ⟨2,by decide⟩,h ⟨3,by decide⟩⟩,h ⟨4,by decide⟩⟩,h ⟨5,by decide⟩⟩
  · rintro ⟨⟨⟨a,b⟩,c⟩,d⟩ ⟨k,hk⟩
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    rcases (by omega : k=2 ∨ k=3 ∨ k=4 ∨ k=5) with rfl|rfl|rfl|rfl <;> assumption

theorem first_six_density : firstDensity 6=55/3456 := by
  let Z (k : ℕ) := k==0
  let P (k : ℕ) := decide (0<k)
  have eq : withHit 6 (s:=short 5) zeroCounts=fiveBox Z Z Z Z P := by
    funext r
    apply propext
    simp only [withHit,earlier_zero,fiveBox,Bool.and_eq_true,Z,P,beq_iff_eq,decide_eq_true_eq]
  rw [firstDensity,if_pos (by decide : 2≤6)]
  change density sixLengths (withHit 6 (s:=short 5) zeroCounts)=_
  rw [eq,five_box_density]
  norm_num [fiveLaw,fourLaw,lawValue,binaryWeight,cubicWeight,quarticWeight,quinticWeight,sexticMean,Z,P]

theorem no_six_density : survival 6=77/3456 := by
  let Z (k : ℕ) := k==0
  have eq : survival 6=density sixLengths (fiveBox Z Z Z Z Z) := by
    have len : short 6=sixLengths := by ext i; rw [six_slots]; exact mem_Icc
    unfold survival
    rw [len]
    congr 1
    funext n
    apply propext
    simp only [fiveBox,Z,Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h; exact ⟨⟨⟨⟨h _,h _⟩,h _⟩,h _⟩,h _⟩
    · rintro ⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩ ⟨k,hk⟩
      obtain ⟨lo,hi⟩ := (six_slots k).mp hk
      rcases (by omega : k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6) with rfl|rfl|rfl|rfl|rfl <;> assumption
  rw [eq,five_box_density]
  norm_num [fiveLaw,fourLaw,lawValue,binaryWeight,cubicWeight,quarticWeight,quinticWeight,sexticMean,Z]

#print axioms sixLengths
#print axioms six_slots
#print axioms fiveBox
#print axioms endpointFiveBox
#print axioms five_box_density
#print axioms endpoint_five_limit
#print axioms first_six_density
#print axioms no_six_density
end
end Erdos478.TetrahedralGap
