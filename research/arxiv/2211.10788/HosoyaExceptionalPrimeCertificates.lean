import LucasFibonacciSelfDividingPrimePowers

/-! Short certificates for the possible cofactor primes above the support {2,3}. -/

namespace Arxiv.«2211.10788».IndexDivisors

def smallCofactors : Finset ℕ := {1,2,3,9,27}
def exceptionalPrimes : Finset ℕ := {67,157,6719,6983}

private def fastValue (n : ℕ) := 2*Nat.fastFib n+Nat.fastFib (n+2)

private theorem fastValue_eq (n : ℕ) : fastValue n=lucasFibonacciSum n := by
  simp [fastValue,Nat.fastFib_eq,lucasFibonacciSum]

private def witnessMultiplier (p : ℕ) := if p=157 then 70 else 27

/-- A single modulus-p² test at a multiple of p rules out a second digit
in the index-value gcd at every index, using the local tower theorem. -/
theorem exceptional_no_square {p : ℕ} (hp : p.Prime) (h : p ∈ exceptionalPrimes) (n : ℕ) :
    ¬p^2 ∣ n.gcd (lucasFibonacciSum n) := by
  have : Fact p.Prime := ⟨hp⟩
  have cert : ∀ q ∈ exceptionalPrimes,
      q ∣ fastValue (q*witnessMultiplier q) ∧ ¬q^2 ∣ fastValue (q*witnessMultiplier q) := by
    decide +kernel
  obtain ⟨hit,miss⟩ := cert p h
  simp only [fastValue_eq] at hit miss
  intro sq
  obtain ⟨h5,_,cap⟩ := (attainable_index_value_power (p:=p) 1).mp ⟨n,sq⟩
  exact miss ((upper_divisor_on_tower (p:=p) h5 (e:=1)
    (n:=p*witnessMultiplier p) (by simp)).mpr ⟨hit,cap⟩)

/-- None of the remaining single-power candidates divides its value. -/
theorem exceptional_first_power_misses {p m : ℕ} (hp : p ∈ exceptionalPrimes)
    (hm : m ∈ smallCofactors) : ¬p*m ∣ lucasFibonacciSum (p*m) := by
  have cert : ∀ q ∈ exceptionalPrimes, ∀ d ∈ smallCofactors, ¬q*d ∣ fastValue (q*d) := by
    decide +kernel
  simpa only [fastValue_eq] using cert p hp m hm

#print axioms exceptional_no_square
#print axioms exceptional_first_power_misses

end Arxiv.«2211.10788».IndexDivisors
