import Erdos722QuartetDirections
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Unit differences for the six-point block construction

Consecutive residues give directions when the modulus is coprime to the
factorial. Products of fields supply directions when each exact prime-power
factor has sufficient size.
-/

namespace Erdos722.Six
open Erdos722.Quartet

def restrict {s k t : ℕ} (D : Directions k t) (h : s ≤ k) : Directions s t where
  K := D.K
  card := D.card
  c i := D.c (Fin.castLE h i)
  units i j hij := D.units (Fin.castLE h i) (Fin.castLE h j) (fun e => hij (Fin.ext (congrArg (fun v : Fin k => v.val) e)))

noncomputable def modular {k t : ℕ} (ht : 0 < t) (h : k.factorial.Coprime t) :
    Directions k t := by
  haveI : NeZero t := ⟨ht.ne'⟩
  have ordered (i j : Fin k) (hij : j < i) : IsUnit ((i.val : ZMod t) - j.val) := by
    rw [← Nat.cast_sub hij.le]
    apply (ZMod.isUnit_iff_coprime ..).mpr
    apply h.of_dvd_left (Nat.dvd_factorial (by omega) (by omega))
  refine ⟨ZMod t,ZMod.card t,fun i => (i.val : ZMod t),?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · simpa using (ordered j i hij).neg
  · exact ordered i j hij

private theorem product {k : ℕ} (S : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ p ∈ S, Nonempty (Directions k (f p))) :
    Nonempty (Directions k (∏ p ∈ S, f p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (show Nonempty (Directions k 1) from ⟨modular (by decide) (by simp)⟩)
  | insert p S hp ih =>
    rw [Finset.prod_insert hp]
    exact ⟨(h p (by simp)).some.prod (ih (fun q hq => h q (by simp [hq]))).some⟩

theorem factorized {k t : ℕ} (ht : 0 < t)
    (h : ∀ p ∈ t.primeFactors, k ≤ p ^ t.factorization p) :
    Nonempty (Directions k t) := by
  have e := Nat.prod_factorization_pow_eq_self ht.ne'
  rw [Nat.prod_factorization_eq_prod_primeFactors] at e
  apply e ▸ product t.primeFactors (fun p => p ^ t.factorization p) ?_
  intro p hp
  have hpos : t.factorization p ≠ 0 := by
    exact Finsupp.mem_support_iff.mp hp
  exact ⟨Directions.primePower k p _ hpos (h p hp) (Nat.prime_of_mem_primeFactors hp)⟩

theorem large_factors {k t : ℕ} (ht : 0 < t) (hd : k.factorial ^ k ∣ t) :
    Nonempty (Directions k t) := by
  apply factorized ht
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have hn : t.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  by_cases h : p ≤ k
  · have he := (prime.pow_dvd_iff_le_factorization ht.ne').mp
      ((pow_dvd_pow_of_dvd (Nat.dvd_factorial prime.pos h) k).trans hd)
    have h₁ : k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
    exact h₁.trans ((Nat.pow_le_pow_left prime.two_le k).trans
      (Nat.pow_le_pow_right prime.pos he))
  · exact (by omega : k ≤ p).trans (by
      simpa using (Nat.pow_le_pow_right prime.pos (by omega : 1 ≤ t.factorization p)))

#print axioms modular
#print axioms large_factors
end Erdos722.Six
