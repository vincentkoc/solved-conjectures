import Erdos722MarkedBasisValues

/-! # Exact isomorphism-class counts for each fixed pattern of marked incidences -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

def markedClasses (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) :=
  univ.image fun u => classOf (markedDesign d hd c u)

private theorem quotient_class (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) (u v : CubeOffsets d) :
    classOf (markedDesign d hd c u)=classOf (markedDesign d hd c v) ↔
      (u : CubeOffsets d ⧸ (markedGradient d hd c).range)=v := by
  rw [marked_class_iff,QuotientAddGroup.eq,AddMonoidHom.mem_range]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,by abel⟩
  · rintro ⟨t,h⟩
    exact ⟨t,by rw [h]; abel⟩

def markedClassEquiv (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) :
    (CubeOffsets d ⧸ (markedGradient d hd c).range) ≃ markedClasses d hd c := by
  let f (q : CubeOffsets d ⧸ (markedGradient d hd c).range) : markedClasses d hd c :=
    ⟨classOf (markedDesign d hd c q.out),mem_image.mpr ⟨_,mem_univ _,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q eq
    have same := (quotient_class d hd c p.out q.out).mp (congrArg Subtype.val eq)
    exact p.out_eq.symm.trans (same.trans q.out_eq)
  · rintro ⟨D,hD⟩
    obtain ⟨u,_,rfl⟩ := mem_image.mp hD
    exact ⟨u,Subtype.ext ((quotient_class d hd c _ u).mpr (Quotient.out_eq _))⟩

theorem marked_class_count (d : ℕ) (hd : 6≤d) (c : affineBasisMarks d → Colour) :
    (markedClasses d hd c).card=4^(blockNumber (2^d)-2^d)*2^groupDimension d c := by
  let G := markedGradient d hd c
  have offsets := G.range.card_eq_card_quotient_mul_card_addSubgroup
  have shifts := G.ker.card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_congr (markedClassEquiv d hd c),Nat.card_eq_fintype_card (α:=markedClasses d hd c),
    Fintype.card_coe,cube_offsets_card] at offsets
  have dom : Nat.card (Cube d → Fibre)=4^(2^d) := by simp [Nat.card_eq_fintype_card,Fibre,Cube]
  rw [dom,Nat.card_congr (QuotientAddGroup.quotientKerEquivRange G).toEquiv,marked_kernel_card] at shifts
  have le : 2^d≤blockNumber (2^d) := by
    have h := Nat.card_le_card_of_injective _ (cycle_gradient_injective d hd)
    rw [dom,cube_offsets_card] at h
    exact (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp h
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<4^(2^d))
  calc
    _ = ((markedClasses d hd c).card*Nat.card G.range)*2^groupDimension d c := by rw [shifts,mul_assoc]
    _ = 4^(blockNumber (2^d))*2^groupDimension d c := by rw [← offsets]
    _ = _ := by rw [mul_right_comm,← pow_add,Nat.sub_add_cancel le]

#print axioms markedClasses
#print axioms markedClassEquiv
#print axioms marked_class_count
end
end Erdos722.FourPoint
