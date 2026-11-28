import LucasFibonacciAlmostPrimeClosure

/-! Exact congruence tests for the canonical upper sequence at prime indices. -/

namespace Arxiv.«2211.10788».AlmostPrimeClosure
open CongruenceClosure ProgressionClosure
open scoped ArithmeticFunction.Omega

/-- In any affine index progression, only the two signed neighboring
parameters can recur modulo every allowed modulus at unbounded primes. -/
theorem prime_cofinal_iff {r d E : ℕ} (hd : 0<d) (he : 0<E) (y : ℤ) :
    (∀ M : ℕ, 0<M → M.Coprime E → ∀ B : ℕ, ∃ p : ℕ, B<p ∧ p.Prime ∧ Hit d r M y p) ↔
      signed ((r:ℤ)+d)=y ∨ signed ((r:ℤ)-d)=y := by
  simp_rw [← Nat.isAlmostPrime_one_iff]
  rw [show (∀ M : ℕ, 0<M → M.Coprime E → ∀ B : ℕ, ∃ p : ℕ, B<p ∧ Nat.IsAlmostPrime 1 p ∧ Hit d r M y p) ↔ _ from
    cofinal_hits_iff (k:=1) hd he y]
  constructor
  · rintro ⟨w,nz,small,val⟩
    have eq := ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp (show Ω w.natAbs=0 by omega)
    have sign : w=1 ∨ w= -1 := by omega
    rcases sign with rfl|rfl
    · exact Or.inl (by simpa using val)
    · exact Or.inr (by simpa [sub_eq_add_neg] using val)
  · rintro (plus|minus)
    · exact ⟨1,by decide,by simp,by simpa using plus⟩
    · exact ⟨-1,by decide,by simp,by simpa [sub_eq_add_neg] using minus⟩

/-- With prime parameters, a fixed exact hit supplies the only additional
possibility beyond the two cofinal limits. -/
theorem prime_modular_iff {r d E : ℕ} (hd : 0<d) (he : 0<E) (y : ℤ) :
    (∀ M : ℕ, 0<M → M.Coprime E → ∃ p : ℕ, p.Prime ∧ Hit d r M y p) ↔
      (∃ p : ℕ, p.Prime ∧ (lucasFibonacciSum (r+d*p):ℤ)=y) ∨
      signed ((r:ℤ)+d)=y ∨ signed ((r:ℤ)-d)=y := by
  have full := modular_hits_iff (k:=1) (r:=r) (d:=d) he y
  have co : CofinalHits 1 r d E y ↔ signed ((r:ℤ)+d)=y ∨ signed ((r:ℤ)-d)=y := by
    simpa only [CofinalHits,Nat.isAlmostPrime_one_iff] using prime_cofinal_iff (r:=r) hd he y
  simpa only [ModularHits,Nat.isAlmostPrime_one_iff,co] using full

/-- The only prime passing every prime-index congruence test without
equaling a prime-indexed upper value is 3. Tests may omit any finite
set of prime divisors of moduli. -/
theorem prime_value_at_prime_indices {E q : ℕ} (he : 0<E) (hq : q.Prime) :
    (∀ M : ℕ, 0<M → M.Coprime E → ∃ p : ℕ, p.Prime ∧ lucasFibonacciSum p ≡ q [MOD M]) ↔
      q=3 ∨ ∃ p : ℕ, p.Prime ∧ lucasFibonacciSum p=q := by
  have four : signed (1:ℤ)=4 := by decide
  have three : signed (-1:ℤ)=3 := by decide
  have result := prime_modular_iff (r:=0) (d:=1) (by decide) he (q:ℤ)
  simp only [Hit,one_mul,zero_add,Nat.cast_zero,Nat.cast_one,zero_sub,four,three,
    Int.natCast_modEq_iff,Nat.cast_inj] at result
  have ne : q≠4 := by rintro rfl; norm_num at hq
  constructor
  · intro tested
    rcases result.mp tested with val|four|three
    · exact Or.inr val
    · omega
    · left; omega
  · rintro (rfl|val)
    · exact result.mpr (Or.inr (Or.inr rfl))
    · exact result.mpr (Or.inl val)

theorem three_no_prime_index : ∀ p : ℕ, p.Prime → lucasFibonacciSum p≠3 := by
  intro p hp
  have bound : lucasFibonacciSum 2≤lucasFibonacciSum p := Nat.add_le_add
    (Nat.mul_le_mul_left 2 (Nat.fib_mono hp.two_le)) (Nat.fib_mono (Nat.add_le_add_right hp.two_le 2))
  have : lucasFibonacciSum 2=5 := by decide
  omega

/-- A modulus separating the unrestricted prime impostor 31 when the
index itself is required to be prime. -/
theorem thirty_one_mod_fifty_eight {p : ℕ} (hp : p.Prime) :
    ¬lucasFibonacciSum p ≡ 31 [MOD 58] := by
  let f := fun n : ℕ => lucasFibonacciSum n % 58
  have periodic : Function.Periodic f 42 := by
    intro n
    change lucasFibonacciSum (n+42) ≡ lucasFibonacciSum n [MOD 58]
    induction n using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more n h₀ h₁ =>
      rw [show n+2+42=n+42+2 by omega,lucas_fibonacci_sum_recurrence,lucas_fibonacci_sum_recurrence (n:=n)]
      exact h₁.add h₀
  intro hit
  have red := periodic.nat_mul (p/42) (p%42)
  change f (p%42+p/42*42)=f (p%42) at red
  rw [Nat.mul_comm (p/42),Nat.mod_add_div] at red
  have v : f (p%42)=31 := red.symm.trans (show f p=31 from hit)
  have residues : ∀ i : Fin 42, f i=31 → i.val=21 ∨ i.val=35 := by decide
  have eq := residues ⟨p%42,Nat.mod_lt _ (by decide)⟩ v
  have dv : 7∣p := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have red := Nat.mod_mod_of_dvd p (by decide : 7∣42)
    change p%42=21 ∨ p%42=35 at eq
    rcases eq with h|h <;> rw [h] at red <;> omega
  have same := (Nat.dvd_prime hp).mp dv
  rcases same with bad|rfl
  · omega
  · exact (by decide : ¬lucasFibonacciSum 7 ≡ 31 [MOD 58]) hit

#print axioms thirty_one_mod_fifty_eight

#print axioms prime_cofinal_iff
#print axioms prime_modular_iff
#print axioms prime_value_at_prime_indices
#print axioms three_no_prime_index

end Arxiv.«2211.10788».AlmostPrimeClosure
