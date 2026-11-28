import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Two uniform bounds for the equations x² ± 44 = b zᵐ with b supported on a
fixed finite set of primes imply a common bound even as m varies. -/

namespace Arxiv.«2211.10788».HosoyaPowerIsolation
open Finset

/-- A positive integer that becomes a unit after inverting the primes in S. -/
def Supported (S : Finset ℕ) (b : ℕ) : Prop := b ≠ 0 ∧ b.primeFactors ⊆ S

/-- These two signs are the two simple-root quadratics X²+44 and X²−44. -/
def QuadraticTwist (x b z m : ℕ) : Prop :=
  x^2 + 44 = b*z^m ∨ x^2 = b*z^m+44

/-- Rational-integer specializations of Bérczes, Bugeaud, Győry, Mello, Ostafe
and Sha, Proposition 4.3 and Theorem 2.2. An S-unit coefficient has S-norm one. -/
structure QuadraticUnitBounds : Prop where
  height : ∀ (S : Finset ℕ) (m : ℕ), 3 ≤ m → ∃ A : ℕ, ∀ x b z,
    Supported S b → 0 < z → QuadraticTwist x b z m → x ≤ A
  exponent : ∀ S : Finset ℕ, ∃ B : ℕ, ∀ x b z m, 3 ≤ m → Supported S b →
    0 < z → ¬Supported S z → QuadraticTwist x b z m → m ≤ B

private theorem supported_mul {S : Finset ℕ} {a b : ℕ} (ha : Supported S a)
    (hb : Supported S b) : Supported S (a*b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  rw [Nat.primeFactors_mul ha.1 hb.1]
  exact union_subset ha.2 hb.2

private theorem supported_pow {S : Finset ℕ} {b : ℕ} (hb : Supported S b) (m : ℕ) :
    Supported S (b^m) := by
  induction m with
  | zero => simp [Supported]
  | succ m ih => rw [pow_succ]; exact supported_mul ih hb

/-- The bound is independent of the supported coefficient and of the exponent.
When the base is itself supported, absorb its entire power into the coefficient
and apply the height bound at exponent four. -/
theorem bounded_smooth_twists (h : QuadraticUnitBounds) (S : Finset ℕ) :
    ∃ A : ℕ, ∀ x b z m, 3 ≤ m → Supported S b → 0 < z → QuadraticTwist x b z m → x ≤ A := by
  classical
  obtain ⟨B,hB⟩ := h.exponent S
  have fixed (m : ℕ) := h.height S (max 3 m) (le_max_left ..)
  choose A hA using fixed
  refine ⟨(range (max B 4+1)).sup A, ?_⟩
  intro x b z m hm hb hz he
  by_cases hs : Supported S z
  · have hs' := supported_mul hb (supported_pow hs m)
    have he' : QuadraticTwist x (b*z^m) 1 4 := by simpa [QuadraticTwist] using he
    exact (hA 4 x _ 1 hs' (by decide) he').trans
      (le_sup (f := A) (mem_range.mpr (by omega : 4 < max B 4+1)))
  · have hmB := hB x b z m hm hb hz hs he
    have hi := hA m x b z hb hz (by simpa [max_eq_right hm] using he)
    exact hi.trans (le_sup (f := A) (mem_range.mpr (by omega)))

#print axioms bounded_smooth_twists

/-- If all valuations outside S are multiples of k, split off the full S-part.
The remaining integer is a kth power. -/
theorem supported_times_power (S : Finset ℕ) {y k : ℕ} (hy : y ≠ 0)
    (hval : ∀ p ∈ y.primeFactors, p ∉ S → k ∣ y.factorization p) :
    ∃ b z : ℕ, Supported S b ∧ 0 < z ∧ y=b*z^k := by
  classical
  let I := y.primeFactors.filter (· ∈ S)
  let O := y.primeFactors.filter (· ∉ S)
  let b := ∏ p ∈ I, p^(y.factorization p)
  let z := ∏ p ∈ O, p^(y.factorization p/k)
  have hpos (p : ℕ) (hp : p ∈ y.primeFactors) := (Nat.prime_of_mem_primeFactors hp).pos
  have hb : b ≠ 0 := (Finset.prod_pos (fun p hp => pow_pos (hpos p (mem_filter.mp hp).1) _) : 0 < b).ne'
  have hz : 0 < z := Finset.prod_pos (fun p hp => pow_pos (hpos p (mem_filter.mp hp).1) _)
  have hs : b.primeFactors ⊆ S := by
    intro p hp
    obtain ⟨hpr,hdiv,_⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨q,hq,hpq⟩ := (hpr.prime.dvd_finsetProd_iff (fun q => q^y.factorization q)).mp hdiv
    have hq' := mem_filter.mp hq
    have hpeq := (Nat.prime_dvd_prime_iff_eq hpr (Nat.prime_of_mem_primeFactors hq'.1)).mp (hpr.dvd_of_dvd_pow hpq)
    exact hpeq ▸ hq'.2
  refine ⟨b,z,⟨hb,hs⟩,hz,?_⟩
  have hrest : z^k = ∏ p ∈ O, p^y.factorization p := by
    dsimp [z]
    rw [← Finset.prod_pow]
    apply prod_congr rfl
    intro p hp
    obtain ⟨hmem,hout⟩ := mem_filter.mp hp
    rw [← pow_mul, Nat.div_mul_cancel (hval p hmem hout)]
  rw [hrest]
  exact (Nat.prod_primeFactors_pow_factorization hy).trans
    (prod_filter_mul_prod_filter_not y.primeFactors (· ∈ S) _).symm

#print axioms supported_times_power

/-- Outside any prescribed finite set of primes, the valuations of every
sufficiently large solution value y of x² − 5y² = ±44 have greatest common
divisor one. The size threshold works for all k simultaneously. -/
theorem outside_prime_for_every_exponent (h : QuadraticUnitBounds) (S : Finset ℕ) :
    ∃ N : ℕ, ∀ y ≥ N, (∃ x : ℕ, x^2 = 5*y^2+44 ∨ x^2+44 = 5*y^2) →
      ∀ k : ℕ, 2 ≤ k → ∃ p ∈ y.primeFactors, p ∉ S ∧ ¬ k ∣ y.factorization p := by
  obtain ⟨A,hA⟩ := bounded_smooth_twists h (insert 5 S)
  refine ⟨A+45, ?_⟩
  intro y hy hex k hk
  obtain ⟨x,hx⟩ := hex
  by_contra! hbad
  obtain ⟨b,z,hb,hz,hyz⟩ := supported_times_power S (by omega : y ≠ 0) hbad
  have hb' : Supported (insert 5 S) b := ⟨hb.1, hb.2.trans (subset_insert ..)⟩
  have h5 : Supported (insert 5 S) 5 := by
    refine ⟨by decide, ?_⟩
    rw [(by decide : Nat.Prime 5).primeFactors]
    exact singleton_subset_iff.mpr (mem_insert_self ..)
  have hcoeff := supported_mul h5 (supported_pow hb' 2)
  have hpow : 5*y^2 = (5*b^2)*z^(2*k) := by rw [hyz, mul_comm 2 k, pow_mul]; ring
  have he : QuadraticTwist x (5*b^2) z (2*k) := by
    rw [hpow] at hx
    exact hx.symm
  have hle := hA x _ z (2*k) (by omega) hcoeff hz he
  have hl : x+45 ≤ y := by omega
  have hs := Nat.pow_le_pow_left hl 2
  rcases hx with hx | hx <;> nlinarith

#print axioms outside_prime_for_every_exponent

end Arxiv.«2211.10788».HosoyaPowerIsolation
