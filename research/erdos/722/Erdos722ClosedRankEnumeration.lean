import Erdos722AffineBasePermutations
import Erdos722LabelledRankSymmetry
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! # Closed enumeration and full group estimates for rank-(2n−d−1) quadruple systems -/

namespace Erdos722.QuadSwitch
open Finset Equiv Module
noncomputable section

/-- Order of the group of affine point permutations and binary fibre flips
in dimension d. The empty product in dimension zero is one. -/
def affineLiftOrder (d : ℕ) := 2^(2^d)*2^d * ∏ i : Fin d, (2^d-2^i.val)

theorem binary_base_order (d : ℕ) : Nat.card (automorphisms (binaryBase d).val)=
    2^d * ∏ i : Fin d, (2^d-2^i.val) := by
  let H := binaryBase d
  let o : Fin (2^d) := 0
  let S := labelSpace H.prop o
  let C : Fin (2^d) ≃ S := affineCoords H.prop (binaryBase_separates d) o
  have card : Nat.card S=2^d := (Nat.card_congr C).symm.trans (Nat.card_fin _)
  have power := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=S)
  rw [card] at power
  have dim : Module.finrank (ZMod 2) S=d :=
    Nat.pow_right_injective (by decide : 2≤2) (by simpa [Nat.card_eq_fintype_card] using power.symm)
  let b := Module.finBasisOfFinrankEq (ZMod 2) S dim
  let G := Matrix.GeneralLinearGroup (Fin d) (ZMod 2)
  let e : G ≃ (S ≃ₗ[ZMod 2] S) := ((Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S)).toEquiv
  have gl : Nat.card (S ≃ₗ[ZMod 2] S)=∏ i : Fin d,(2^d-2^i.val) :=
    (Nat.card_congr e).symm.trans (by simpa [G] using Matrix.card_GL_field (𝔽:=ZMod 2) d)
  rw [← Nat.card_congr (affineBasePermutations H.prop (binaryBase_separates d) o),Nat.card_prod,gl,card,Nat.mul_comm]

theorem lift_order_closed (d : ℕ) : liftOrder d=affineLiftOrder d := by
  rw [liftOrder,binary_base_order,affineLiftOrder]
  ring

/-- The exact labelled mass, the count of all isomorphism classes up to a
cubic-exponential error, and the two exceptional fractions use only d. -/
theorem full_rank_enumeration (d : ℕ) (hd : 7≤d) :
    let n := 2^d
    let b := blockNumber n
    let E := n^3/1024
    let N := (nextRankClasses d).card
    let L := (nextRankSystems d).card
    let G := affineLiftOrder d
    0<N ∧ L*G=(2^b-2^(n-(d+1)))*(2^(d+1)).factorial ∧
    (2^(d+1)*2^b≤(N+1)*G ∧ ((N+1)*G-2^(d+1)*2^b)*2^E≤2^b) ∧
    (exceptionalRankClasses d).card*n*2^E≤N ∧
    (exceptionalRankSystems d).card*(2*(n*2^E)-1)≤L := by
  dsimp only
  rw [← lift_order_closed]
  exact ⟨card_pos.mpr (next_rank_nonempty d hd),labelled_rank_mass d,global_rank_count d hd,
    global_rank_symmetry d hd,labelled_rank_symmetry d hd⟩

/-- In particular a system on the original finite point labels realizes the
usual binary incidence rank and the full elementary abelian group. -/
theorem full_rank_example (d : ℕ) (hd : 7≤d) :
    ∃ D : Finset (Finset (Fin (2^(d+1)))), D.IsBlockDesign 3 4 ∧
      (binaryIncidence D).rank=2^(d+1)-(d+1) ∧
      Nonempty (Multiplicative (Fin (d+1) → ZMod 2) ≃* automorphisms D) := by
  classical
  let N := nextRankClasses d
  let B := exceptionalRankClasses d
  have pos : 0<N.card := card_pos.mpr (next_rank_nonempty d hd)
  have bound := global_rank_symmetry d hd
  have large : 1<2^d := Nat.one_lt_two_pow (by omega)
  have R : 1<2^d*2^((2^d)^3/1024) := by
    exact large.trans_le (Nat.le_mul_of_pos_right _ (by positivity))
  have proper : B.card<N.card := by
    by_contra! low
    have small := (Nat.mul_le_mul_right (2^d*2^((2^d)^3/1024)) low).trans (by simpa [B,N,Nat.mul_assoc] using bound)
    have strict : N.card<N.card*(2^d*2^((2^d)^3/1024)) := by simpa using Nat.mul_lt_mul_of_pos_left R pos
    exact strict.not_ge small
  obtain ⟨C,hC,good⟩ := exists_mem_notMem_of_card_lt_card proper
  obtain ⟨D,hD,rfl⟩ := mem_image.mp hC
  have standard : standardRankGroup d (classOf D) := by
    by_contra bad; exact good (mem_filter.mpr ⟨mem_image_of_mem _ hD,bad⟩)
  exact ⟨D,(mem_filter.mp hD).2.1,(mem_filter.mp hD).2.2,(standard_group_coordinates d D).mp standard⟩

#print axioms affineLiftOrder
#print axioms binary_base_order
#print axioms lift_order_closed
#print axioms full_rank_enumeration
#print axioms full_rank_example
end
end Erdos722.QuadSwitch
