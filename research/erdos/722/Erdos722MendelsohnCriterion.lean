import Erdos722SmallWittExtension
import Erdos722UnitExcessArithmetic

/-! # Mendelsohn's equivalence for every positive block size

At positive even block size the penultimate divisibility test rules out the
punctured design. Derivation in the reverse direction needs no parity assumption.
-/

namespace Erdos722.ComplementExtension
open Finset IntegralDesign

private theorem odd_of_punctured {k : ℕ} (hk : 0<k)
    {H : Finset (Finset (Fin (2*k+1)))} (h : H.IsBlockDesign (k-1) k) : Odd k := by
  rcases Nat.even_or_odd k with ⟨a,ha⟩|odd
  · have two : 2≤k := by omega
    have tests := (signed_steiner_iff (2*k+1) (k-1) k (by omega) (by omega)).mp ⟨_,design_weights h⟩
    have bad := tests (k-2) (by omega)
    rw [show k-(k-2)=2 by omega,show k-1-(k-2)=1 by omega,
      show 2*k+1-(k-2)=k+3 by omega,Nat.choose_one_right,Nat.choose_one_right] at bad
    omega
  · exact odd

/-- The point set and the distinguished point are fixed. Every input at
positive block size has exactly one extension with that derived family. -/
theorem mendelsohn_unique {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : 0<k) (hc : Fintype.card α=2*k+1) {H : Finset (Finset α)}
    (h : H.IsBlockDesign (k-1) k) :
    ∃! G : Finset (Finset (Option α)), G.IsBlockDesign k (k+1) ∧
      ∀ B : Finset α, insert none (B.map Function.Embedding.some)∈G ↔ B∈H :=
  unique_steiner_extension hc (odd_of_punctured hk (PointedProduct.relabel_design (Fintype.equivFinOfCardEq hc) h)) h

theorem mendelsohn_iff {k : ℕ} (hk : 0<k) :
    (∃ H : Finset (Finset (Fin (2*k+1))), H.IsBlockDesign (k-1) k) ↔
      ∃ G : Finset (Finset (Fin (2*k+2))), G.IsBlockDesign k (k+1) := by
  constructor
  · rintro ⟨H,h⟩
    exact (SmallWitt.canonical_iff (odd_of_punctured hk h)).mp ⟨H,h⟩
  · rintro ⟨G,h⟩
    let e : Option (Fin (2*k+1)) ≃ Fin (2*k+2) := Fintype.equivFinOfCardEq (by simp)
    have ext := PointedProduct.relabel_design e.symm h
    exact ⟨_,derived_design (r:=k-1) (by simpa only [show k-1+1=k by omega] using ext)⟩

/-- Either ordinary existence statement forces the arithmetic obstruction
on the order of the central design. -/
theorem prime_of_punctured {k : ℕ} (hk : 0<k)
    (h : ∃ H : Finset (Finset (Fin (2*k+1))), H.IsBlockDesign (k-1) k) : (k+2).Prime := by
  obtain ⟨G,hG⟩ := (mendelsohn_iff hk).mp h
  have tests := (signed_steiner_iff (2*k+2) k (k+1) (by omega) (by omega)).mp ⟨_,design_weights hG⟩
  apply (UnitExcess.central_tests k).mp
  simpa only [Nat.mul_add,Nat.mul_one] using tests

#print axioms mendelsohn_unique
#print axioms mendelsohn_iff
#print axioms prime_of_punctured
end Erdos722.ComplementExtension
