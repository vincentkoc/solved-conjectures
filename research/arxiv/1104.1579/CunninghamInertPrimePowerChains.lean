import CunninghamLeadingTriple
import CunninghamPlusMultiplier
import CunninghamInfiniteSharedLinearChains

/-! All-index irreducibility in the Jones plus chain for odd prime powers
and the even prime powers with nonsquare negative unit modulo the half power. -/

namespace CunninghamChain.LinearRoots
open Polynomial

/-- At a square prime power, every factorization with two nonunit leading
coefficients forces a square root of the negative sign modulo the half power. -/
theorem even_power_split_obstruction {p r : ℕ} (hp : p.Prime) (hr : 0<r)
    (k : Bool) {n : ℕ} (hn : n≠0) (A B : ℤ[X])
    (hab : polynomialTerm k (C ((p^(2*r):ℕ):ℤ)*X+C (-(p^(2*r):ℕ):ℤ)) n=A*B)
    (ha : ¬IsUnit A.leadingCoeff) (hb : ¬IsUnit B.leadingCoeff) :
    ∃ u : ℤ, ((p^r:ℕ):ℤ) ∣ u^2+sign k := by
  obtain ⟨c,l,b⟩ := balanced_reverse_coefficients (pow_pos hp.pos _) k hn A B hab
  have hε : ¬(p:ℤ)∣sign k := by
    cases k <;> simpa [sign] using (Nat.prime_iff_prime_int.mp hp).not_dvd_one
  apply (split_three_coefficients_iff hp hr (sign k) hε).mp
  have ex : ((p^(2*r):ℕ):ℤ)=((p^r:ℕ):ℤ)^2 := by rw [two_mul,pow_add]; push_cast; ring
  exact ⟨A.reverse,B.reverse,c.trans ex,l.trans (congrArg Neg.neg ex),b,by simpa using ha,by simpa using hb⟩

/-- From the seed p^e(X−1), every plus iterate is irreducible if the coefficient
is at least 28 and either e is odd, p=2, or p is 3 modulo 4. -/
theorem infinite_plus_prime_power {p e : ℕ} (hp : p.Prime) (size : 28≤p^e)
    (condition : Odd e ∨ p=2 ∨ p%4=3) (n : ℕ) :
    Irreducible (term true (p^e:ℕ) (-(p^e:ℕ):ℤ) n) := by
  apply balanced_irreducible_of_factor_energy (by omega) true n
  · intro hn A B hab
    obtain ⟨c,l,b⟩ := balanced_reverse_coefficients (pow_pos hp.pos _) true hn A B hab
    have force := (prime_power_plus_triple_iff hp size).mpr condition
    simpa using force A.reverse B.reverse c l (by simpa [sign] using b)
  · exact fun _ => PlusMultiplier.plus_factor_energy size n

#print axioms even_power_split_obstruction
#print axioms infinite_plus_prime_power

end CunninghamChain.LinearRoots
