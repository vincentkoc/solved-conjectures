import CunninghamJonesBlockPatterns

/-! Congruence conditions on a list of prime divisors guaranteeing irreducibility
in every degree. -/

namespace CunninghamChain.JonesSplitParity
open Finset Polynomial

/-- The indices are 0 through n. Every prime after the immediate successor of
q(i) is one modulo q(i), while the immediate successor squares to minus one. -/
structure PrimePattern (q : ℕ → ℕ) (n k : ℕ) : Prop where
  prime : ∀ i ≤ n, (q i).Prime
  large : ∀ i ≤ n, 2 < q i
  size : 5^n < 2^(k+1)
  firstResidues : ∀ i < n, (q i : ZMod (2^(k+1)))=5
  productResidue : ((∏ i ∈ range (n+1), q i : ℕ) : ZMod (2^(k+1)))=1
  nextSquare : ∀ i < n, (q (i+1) : ZMod (q i))^2 = -1
  laterResidues : ∀ i j, i+1 < j → j ≤ n → (q j : ZMod (q i))=1

private theorem PrimePattern.toBlocks {q : ℕ → ℕ} {n k : ℕ} (h : PrimePattern q n k) :
    BlockPattern q q n k 5 :=
  ⟨fun i hi => (h.prime i hi).odd_of_ne_two (by have := h.large i hi; omega),
    h.large, fun _ _ => dvd_refl _, by decide, h.size, h.firstResidues, h.productResidue,
    h.nextSquare, h.laterResidues⟩

theorem irreducible_of_prime_pattern {q : ℕ → ℕ} {n k : ℕ} (h : PrimePattern q n k) {j : ℕ}
    (hj : 0<j) : Irreducible ((jonesSumPolynomial (∏ i ∈ range (n+1),q i) j).map (Int.castRingHom ℚ)) := by
  have pr (i) (hi : i ∈ range (n+1)) := h.prime i (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hm := Nat.le_of_dvd (prod_pos fun i hi => (pr i hi).pos)
    (dvd_prod_of_mem q (mem_range.mpr (show 0<n+1 by omega)))
  apply irreducible_all_degrees_of_coprime_splits (by have := h.large 0 (Nat.zero_le n); omega) _ hj
  exact h.toBlocks.certificate (fun i hi => (h.prime i hi).isPrimePow)

#print axioms irreducible_of_prime_pattern

end CunninghamChain.JonesSplitParity
