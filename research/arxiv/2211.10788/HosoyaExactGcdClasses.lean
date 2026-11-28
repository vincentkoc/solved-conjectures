import LucasFibonacciExactGcdSpectrum

/-! Sharp local consequences of the exact gcd criterion on two small return moduli. -/

namespace Arxiv.«2211.10788».IndexDivisors

def modTwelveMinimum (a : ℕ) : ℕ :=
  if a%12=3 then 3 else if a%12=4 ∨ a%12=10 then 2 else 1

private lemma twelve_table (a : Fin 12) : residueGcd 12 a.val = modTwelveMinimum a.val := by
  rw [←fastResidueGcd_eq]
  exact (by decide +kernel : ∀ t : Fin 12, fastResidueGcd 12 t.val = modTwelveMinimum t.val) a

private lemma twelve_residue (a : ℕ) : residueGcd 12 (a%12) = modTwelveMinimum a := by
  simpa only [modTwelveMinimum,Nat.mod_mod] using twelve_table ⟨a%12,Nat.mod_lt _ (by decide)⟩

/-- In each index class modulo twelve, the displayed gcd divides every actual gcd
and is attained arbitrarily far out. -/
theorem sharp_mod_twelve_minimum (a : ℕ) :
    (∀ n, n ≡ a [MOD 12] → modTwelveMinimum a ∣ n.gcd (lucasFibonacciSum n)) ∧
    ∀ B, ∃ n, B<n ∧ n ≡ a [MOD 12] ∧ n.gcd (lucasFibonacciSum n)=modTwelveMinimum a := by
  have ret : 12 ∣ Nat.fib 12 := by decide
  constructor
  · intro n cl
    rw [←twelve_residue,←(show n%12=a%12 from cl),residueGcd_mod ret]
    exact Nat.gcd_dvd_right ..
  · intro B
    obtain ⟨q,big,_,cl,val⟩ := prime_realizes_residue_gcd (by decide : 0<12) ret (a%12) B
    have le := Nat.le_mul_of_pos_left q (Nat.gcd_pos_of_pos_right (a%12) (by decide : 0<12))
    exact ⟨_,by omega,cl.trans (Nat.mod_modEq ..),val.trans (twelve_residue a)⟩

private lemma at_own_modulus {A d : ℕ} (hA : 0 < A) (hd : d ∣ A) (ret : A ∣ Nat.fib A) (a : ℕ) :
    (∃ n, 0<n ∧ n ≡ a [MOD A] ∧ n.gcd (lucasFibonacciSum n)=d) ↔ residueGcd A (a%A)=d := by
  rw [exact_gcd_iff_at_return hA (dvd_refl A) hd ret]
  constructor
  · rintro ⟨t,cl,eq⟩
    have he : t.val=a%A := (Nat.mod_eq_of_lt t.isLt).symm.trans cl
    exact he ▸ eq
  · exact fun h => ⟨⟨a%A,Nat.mod_lt _ hA⟩,Nat.mod_modEq ..,h⟩

/-- Modulo 168, exact gcd seven is possible only at 84 and 140, and exact
gcd fourteen only at 28. Every listed fiber has arbitrarily large representatives. -/
theorem seven_fourteen_classes (a : ℕ) :
    ((∃ n, 0<n ∧ n ≡ a [MOD 168] ∧ n.gcd (lucasFibonacciSum n)=7) ↔ a%168=84 ∨ a%168=140) ∧
    ((∃ n, 0<n ∧ n ≡ a [MOD 168] ∧ n.gcd (lucasFibonacciSum n)=14) ↔ a%168=28) := by
  have ret : 168 ∣ Nat.fib 168 := by
    rw [←show (Nat.fastFibAux 168).1=Nat.fib 168 by simp [Nat.fastFibAux_eq]]
    decide +kernel
  have tab : ∀ t : Fin 168,
      (fastResidueGcd 168 t.val=7 ↔ t.val=84 ∨ t.val=140) ∧
      (fastResidueGcd 168 t.val=14 ↔ t.val=28) := by decide +kernel
  rw [at_own_modulus (by decide) (by decide) ret,at_own_modulus (by decide) (by decide) ret]
  simpa only [fastResidueGcd_eq] using tab ⟨a%168,Nat.mod_lt _ (by decide)⟩

#print axioms sharp_mod_twelve_minimum
#print axioms seven_fourteen_classes

end Arxiv.«2211.10788».IndexDivisors
