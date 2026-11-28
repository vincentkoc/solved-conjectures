import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-! # Prescribed quotients of factorials at a fixed gap -/

namespace Erdos478.QuotientSpacing
open Finset Polynomial
open scoped Classical
noncomputable section

/-- A field-valued expression for the quotient, in terms of the upper endpoint. -/
def quotient (p i j : ℕ) : ZMod p := (j.factorial : ZMod p) * (i.factorial : ZMod p)⁻¹

theorem quotient_factorial {p i j : ℕ} (hp : p.Prime) (ij : i≤j) (jp : j<p) :
    quotient p i j=(j.descFactorial (j-i) : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have nz : (i.factorial : ZMod p) ≠ 0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff,hp.dvd_factorial]
    omega
  change (j.factorial : ZMod p) / (i.factorial : ZMod p) = _
  apply (div_eq_iff nz).mpr
  have eq := congrArg (fun n : ℕ => (n:ZMod p)) (Nat.factorial_mul_descFactorial (by omega : j-i≤j))
  rw [show j-(j-i)=i by omega,Nat.cast_mul] at eq
  exact eq.symm.trans (mul_comm ..)

def quotientStarts (p k : ℕ) (D : Finset (ZMod p)) :=
  (Ico 1 (p-k)).filter fun i => quotient p i (i+k) ∈ D

theorem one_quotient {p k : ℕ} (hp : p.Prime) (hk : 0<k) (u : ZMod p) :
    (quotientStarts p k {u}).card ≤ k := by
  let : Fact p.Prime := ⟨hp⟩
  let P := descPochhammer (ZMod p) k-C u
  have deg : P.natDegree=k := by
    rw [show P=descPochhammer (ZMod p) k-C u from rfl,natDegree_sub_eq_left_of_natDegree_lt,
      descPochhammer_natDegree]
    simpa [descPochhammer_natDegree] using hk
  have nz : P≠0 := by intro eq; rw [eq,natDegree_zero] at deg; omega
  calc
    _ ≤ P.roots.toFinset.card := by
      apply card_le_card_of_injOn (fun i : ℕ => ((i+k:ℕ):ZMod p))
      · intro i hi
        obtain ⟨valid,matchU⟩ := mem_filter.mp hi
        have up : i+k<p := by obtain ⟨_,h⟩ := mem_Ico.mp valid; omega
        have eq := (mem_singleton.mp matchU)
        rw [quotient_factorial hp (Nat.le_add_right i k) up,Nat.add_sub_cancel_left] at eq
        apply Multiset.mem_toFinset.mpr
        apply (mem_roots nz).mpr
        rw [IsRoot.def,show P=descPochhammer (ZMod p) k-C u from rfl,eval_sub,eval_C,
          descPochhammer_eval_eq_descFactorial,eq,sub_self]
      · intro i hi j hj eq
        have ai := (mem_Ico.mp (mem_filter.mp hi).1).2
        have aj := (mem_Ico.mp (mem_filter.mp hj).1).2
        have equal := (ZMod.natCast_eq_natCast_iff' ..).mp eq
        rw [Nat.mod_eq_of_lt (by omega : i+k<p),Nat.mod_eq_of_lt (by omega : j+k<p)] at equal
        omega
    _ ≤ P.natDegree := P.roots.toFinset_card_le.trans P.card_roots'
    _ = k := deg

theorem quotient_capacity {p k : ℕ} (hp : p.Prime) (hk : 0<k) (D : Finset (ZMod p)) :
    (quotientStarts p k D).card ≤ D.card*k := by
  have sub : quotientStarts p k D ⊆ D.biUnion (fun u => quotientStarts p k {u}) := by
    intro i hi
    obtain ⟨valid,mem⟩ := mem_filter.mp hi
    exact mem_biUnion.mpr ⟨_,mem,mem_filter.mpr ⟨valid,mem_singleton_self _⟩⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _ ∈ D,k := sum_le_sum fun u _ => one_quotient hp hk u
    _ = _ := by simp

#print axioms quotient
#print axioms quotient_factorial
#print axioms quotientStarts
#print axioms one_quotient
#print axioms quotient_capacity
end
end Erdos478.QuotientSpacing
