import Erdos722QuadrupleParityChecks
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Counting binary assignments with a prescribed permutation and twist -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
open scoped Classical
variable {I : Type*} [Fintype I]

abbrev Cycles (τ : Perm I) := Quotient (Perm.SameCycle.setoid τ)

theorem cycle_budget (τ : Perm I) [DecidableEq I] :
    Nat.card (Cycles τ)+τ.support.card/2≤Fintype.card I := by
  classical
  let Q := Cycles τ
  let q (x : I) : Q := Quotient.mk _ x
  let R (c : Q) : I := Quotient.out c
  have sec (c : Q) : q (R c)=c := Quotient.out_eq c
  have ri : Injective R := fun a b eq => (sec a).symm.trans ((congrArg q eq).trans (sec b))
  have shift (x : I) : q (τ x)=q x := Quotient.sound (Perm.SameCycle.rfl.apply_left)
  let all := (univ : Finset Q)
  let moved := all.filter fun c => τ (R c)≠R c
  let fixed := all.filter fun c => τ (R c)=R c
  have partition : fixed.card+moved.card=all.card := card_filter_add_card_filter_not ..
  have dis : Disjoint (all.image R) (moved.image (τ ∘ R)) := by
    apply disjoint_left.mpr
    rintro x hx hy
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,hb,he⟩ := mem_image.mp hy
    have same : b=a := (sec b).symm.trans ((shift (R b)).symm.trans ((congrArg q he).trans (sec a)))
    exact (mem_filter.mp hb).2 (same ▸ he)
  have cap := card_le_univ ((all.image R) ∪ (moved.image (τ ∘ R)))
  rw [card_union_of_disjoint dis,card_image_of_injective _ ri,card_image_of_injective _ (τ.injective.comp ri)] at cap
  have codes : fixed.image R ⊆ τ.supportᶜ := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    exact mem_compl.mpr (fun h => (Perm.mem_support.mp h) (mem_filter.mp ha).2)
  have lim := card_le_card codes
  rw [card_image_of_injective _ ri,card_compl] at lim
  have sup := card_le_univ τ.support
  have allcard : all.card=Nat.card (Cycles τ) := card_univ.trans Nat.card_eq_fintype_card.symm
  omega

def solutions (τ : Perm I) (δ : I → ZMod 2) :=
  (univ : Finset (I → Bool)).filter fun s => ∀ i, bitValue (s (τ i))=δ i+bitValue (s i)

/-- An orbit contributes at most one free bit, even for an inhomogeneous block equation. -/
theorem solutions_cycles (τ : Perm I) (δ : I → ZMod 2) :
    (solutions τ δ).card≤2^Nat.card (Cycles τ) := by
  classical
  let Q := Cycles τ
  let q (x : I) : Q := Quotient.mk _ x
  let read (s : solutions τ δ) (c : Q) := s.val (Quotient.out c)
  have inj : Injective read := by
    intro a b eq
    apply Subtype.ext
    funext x
    let r := Quotient.out (q x)
    have orb : τ.SameCycle r x := Quotient.exact (Quotient.out_eq (q x))
    obtain ⟨k,hk⟩ := orb.exists_nat_pow_eq
    have same (n : ℕ) : a.val ((τ^n) r)=b.val ((τ^n) r) := by
      induction n with
      | zero => simpa [read,r] using congrFun eq (q x)
      | succ n ih =>
        rw [pow_succ',Perm.mul_apply]
        apply (show Injective bitValue by decide)
        rw [(mem_filter.mp a.prop).2,(mem_filter.mp b.prop).2,ih]
    exact hk ▸ same k
  have bound := Nat.card_le_card_of_injective read inj
  simpa [Nat.card_eq_fintype_card,Q] using bound

theorem solutions_support_bound (τ : Perm I) [DecidableEq I] (δ : I → ZMod 2) :
    (solutions τ δ).card*2^(τ.support.card/2)≤2^Fintype.card I := by
  apply (Nat.mul_le_mul_right _ (solutions_cycles τ δ)).trans
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by decide) (cycle_budget τ)

#print axioms Cycles
#print axioms cycle_budget
#print axioms solutions
#print axioms solutions_cycles
#print axioms solutions_support_bound
end
end Erdos722.QuadSwitch
