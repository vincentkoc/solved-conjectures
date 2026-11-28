import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-! # Detecting an injective system of finite additive measurements on a small set of coordinates -/

namespace Erdos722.SparseDetection
open Finset
open scoped Classical
noncomputable section
variable {A I F : Type*} [AddGroup A] [Finite A] [AddGroup F]

/-- Each additional nonzero coordinate cuts the remaining common kernel by
an index of at least two. The proof needs no basis for the ambient group. -/
private theorem detect_inside (f : I → A →+ F) (separates : ∀ a, (∀ i,f i a=0) → a=0)
    (K : AddSubgroup A) : ∃ S : Finset I, 2^S.card ≤ Nat.card K ∧
      ∀ a∈K, (∀ i∈S,f i a=0) → a=0 := by
  classical
  by_cases trivial : ∀ a∈K,a=0
  · exact ⟨∅,by rw [card_empty,pow_zero]; exact Nat.card_pos,fun a ha _ => trivial a ha⟩
  push Not at trivial
  obtain ⟨a,ha,ne⟩ := trivial
  obtain ⟨i,hi⟩ : ∃ i, f i a≠0 := by
    by_contra! bad
    exact ne (separates a bad)
  let J := K ⊓ (f i).ker
  have strict : (J:Set A) ⊂ (K:Set A) := by
    apply Set.ssubset_iff_exists.mpr
    exact ⟨fun _ h => h.1,a,ha,fun h => hi h.2⟩
  have smaller : Nat.card J < Nat.card K := Set.ncard_lt_ncard strict
  have half : 2*Nat.card J ≤ Nat.card K := by
    obtain ⟨m,hm⟩ := AddSubgroup.card_dvd_of_le (show J≤K from inf_le_left)
    have two : 2≤m := by
      by_contra! hm'
      interval_cases m <;> simp_all
    rw [hm,mul_comm]
    exact Nat.mul_le_mul_left _ two
  obtain ⟨S,bound,detect⟩ := detect_inside f separates J
  refine ⟨insert i S,?_,?_⟩
  · calc
      _ ≤ 2^(S.card+1) := Nat.pow_le_pow_right (by decide) (card_insert_le ..)
      _ = 2*2^S.card := by rw [pow_succ,mul_comm]
      _ ≤ _ := (Nat.mul_le_mul_left 2 bound).trans half
  · intro x hx tests
    exact detect x ⟨hx,tests i (mem_insert_self ..)⟩ (fun j hj => tests j (mem_insert_of_mem hj))
termination_by Nat.card K

theorem detecting_coordinates (f : I → A →+ F) (separates : ∀ a, (∀ i,f i a=0) → a=0) :
    ∃ S : Finset I, 2^S.card ≤ Nat.card A ∧ ∀ a, (∀ i∈S,f i a=0) → a=0 := by
  obtain ⟨S,bound,det⟩ := detect_inside f separates ⊤
  refine ⟨S,?_,fun a h => det a (AddSubgroup.mem_top a) h⟩
  simpa using bound

#print axioms detecting_coordinates
end
end Erdos722.SparseDetection
