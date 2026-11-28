import Erdos722SignaturePresentation
import Erdos722SwitchedIncidenceRanks
import Erdos722SwitchOrbitAction

/-! # All Steiner quadruple systems one binary incidence rank above the minimum -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem iso_checks {D E : Finset (Finset V)} (iso : Isomorphic D E) :
    Nat.card (Checks D)=Nat.card (Checks E) := by
  obtain ⟨e,rfl⟩ := iso
  exact (Nat.card_congr (checkRelabel e D)).symm

theorem iso_incidence_rank {D E : Finset (Finset V)} (iso : Isomorphic D E) :
    (binaryIncidence D).rank=(binaryIncidence E).rank := by
  have eq := iso_checks iso
  rw [checks_card_rank,checks_card_rank] at eq
  have := Nat.pow_right_injective (by decide : 2≤2) eq
  have hd := (binaryIncidence D).rank_le_card_width
  have he := (binaryIncidence E).rank_le_card_width
  omega

theorem checks_le_twice_points {D : Finset (Finset V)} (hD : D.IsBlockDesign 3 4) (o : V) :
    Nat.card (Checks D)≤2*Nat.card V := by
  rw [label_card_checks hD o]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ (label_surjective hD o))

/-- The global lower bound and its attainment by the ordinary binary affine base. -/
theorem minimum_binary_rank (m : ℕ) {D : Finset (Finset (Fin (2^m)))} (hD : D.IsBlockDesign 3 4) :
    2^m-(m+1)≤(binaryIncidence D).rank ∧ (binaryIncidence (binaryBase m).val).rank=2^m-(m+1) := by
  have le := checks_le_twice_points hD 0
  rw [checks_card_rank,Fintype.card_fin,Nat.card_fin,← pow_succ'] at le
  have := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp le
  refine ⟨by omega,(binary_rank_iff_checks m (m+1) (by have := Nat.lt_two_pow_self (n:=m); omega) _).mpr
    (binaryBase_checks m)⟩

/-- Every labelled quadruple system in this rank stratum admits a switched
affine presentation. Conversely every non-coboundary switch belongs to the stratum. -/
theorem next_rank_iff_switch (d : ℕ) (D : Finset (Finset (Fin (2^(d+1))))) :
    D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank=2^(d+1)-(d+1) ↔
      ∃ s : (binaryBase d).val → Bool, ¬Coboundary s ∧ Isomorphic D (binaryDouble d s) := by
  constructor
  · rintro ⟨hD,rank⟩
    have count := (binary_rank_iff_checks _ _ (Nat.le_of_lt Nat.lt_two_pow_self) _).mp rank
    obtain ⟨e,s,he⟩ := paired_presentation hD (binaryBase d).prop (binaryBase_separates d) 0 0
      (by simp [pow_succ,mul_comm]) (count.trans (binaryBase_checks d).symm)
    have iso : Isomorphic D (binaryDouble d s) := by
      refine ⟨e.trans (binaryStepLabels d),?_⟩
      rw [← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,Equiv.trans_apply,he]
      rfl
    exact ⟨s,(binaryDouble_next_rank d s).mp ((iso_incidence_rank iso).symm.trans rank),iso⟩
  · rintro ⟨s,cs,iso⟩
    have rank := (iso_incidence_rank iso).trans ((binaryDouble_next_rank d s).mpr cs)
    obtain ⟨e,he⟩ := (designIsoSetoid _).iseqv.symm (x:=D) (y:=binaryDouble d s) iso
    exact ⟨he ▸ relabel_quadruples e (binaryDouble_design d s),rank⟩

#print axioms iso_checks
#print axioms iso_incidence_rank
#print axioms checks_le_twice_points
#print axioms minimum_binary_rank
#print axioms next_rank_iff_switch
end
end Erdos722.QuadSwitch
