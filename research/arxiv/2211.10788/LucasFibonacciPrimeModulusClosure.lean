import HosoyaSimultaneousNonresidues
import LucasFibonacciCongruenceClosure

/-! Prime-modulus separation for the upper Lucas–Fibonacci sequence. -/

namespace Arxiv.«2211.10788»
namespace PrimeObstruction

/-- The progression modulus made from both absolute Pell discriminants. -/
def obstructionModulus (y : ℕ) : ℕ := signModulus
  ((5*y^2+44).primeFactors ∪ (5*(y:ℤ)^2-44).natAbs.primeFactors)

/-- A natural number outside both diagonals is excluded at every prime in a reduced progression. -/
theorem prime_obstruction_progression (y : ℕ)
    (hy : ¬((∃ j, y = lucasFibonacciSum j) ∨ IsLowerNeighborValue y)) :
    ∃ r, 0<obstructionModulus y ∧ r.Coprime (obstructionModulus y) ∧
      ∀ p : ℕ, p.Prime → p ≡ r [MOD obstructionModulus y] →
        ∀ n : ℕ, ¬ lucasFibonacciSum n ≡ y [MOD p] := by
  let A := 5*y^2+44
  let C := 5*(y:ℤ)^2-44
  have hA : ¬IsSquare A := by
    rintro ⟨a,ha⟩
    exact hy ((either_diagonal_iff_pell y).mpr ⟨a,Or.inl (by simpa [A,pow_two] using ha.symm)⟩)
  have hB : ¬IsSquare C.natAbs := by
    by_cases hs : y<3
    · have small (u : Fin 3) : ¬IsSquare (5*(u.val:ℤ)^2-44).natAbs := by
        fin_cases u <;> norm_num
      exact small ⟨y,hs⟩
    · have hpos : 0≤C := by
        dsimp [C]
        have h3 : (3:ℤ) ≤ y := by exact_mod_cast (by omega : 3≤y)
        nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h3)]
      rintro ⟨v,hv⟩
      have hh : (C.natAbs:ℤ)=(v:ℤ)*v := by exact_mod_cast hv
      rw [Int.natCast_natAbs,abs_of_nonneg hpos] at hh
      apply hy ((either_diagonal_iff_pell y).mpr ⟨v,Or.inr ?_⟩)
      exact_mod_cast (show (v:ℤ)^2+44=5*(y:ℤ)^2 by dsimp [C] at hh; nlinarith)
  obtain ⟨M,r,hEq,hM,hr,hclass⟩ := two_nonsquares_prime_progression hA hB
  change M = obstructionModulus y at hEq
  subst M
  refine ⟨r,hM,hr,?_⟩
  intro p hp he n hn
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨h4,hnA,hnB⟩ := hclass p hp he
  have hu := (ZMod.natCast_eq_natCast_iff ..).mpr hn
  obtain ⟨x,hx|hx⟩ := (either_diagonal_iff_pell (lucasFibonacciSum n)).mp (Or.inl ⟨n,rfl⟩)
  · have hh : (x:ZMod p)^2=5*(lucasFibonacciSum n:ZMod p)^2+44 := by
      simpa using congrArg (fun v : ℕ => (v:ZMod p)) hx
    rw [hu] at hh
    exact hnA ⟨(x:ZMod p),by simpa [A,pow_two] using hh.symm⟩
  · have hh : (x:ZMod p)^2+44=5*(lucasFibonacciSum n:ZMod p)^2 := by
      simpa using congrArg (fun v : ℕ => (v:ZMod p)) hx
    rw [hu] at hh
    have hs : IsSquare (C:ZMod p) := ⟨(x:ZMod p),by dsimp [C]; push_cast; linear_combination -hh⟩
    rcases Int.natAbs_eq C with hc|hc
    · have he' : (C:ZMod p)=(C.natAbs:ZMod p) := by
        simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun v : ℤ => (v:ZMod p)) hc
      exact hnB (he' ▸ hs)
    · have he' : (C:ZMod p)= -(C.natAbs:ZMod p) := by
        simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun v : ℤ => (v:ZMod p)) hc
      rw [he'] at hs
      have hneg := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega : p%4≠3)
      exact hnB (by simpa using hneg.mul hs)

/-- Testing only prime moduli gives exactly the same range closure as testing every modulus. -/
theorem prime_moduli_iff_all (y : ℕ) :
    (∀ p : ℕ, p.Prime → ∃ n, lucasFibonacciSum n ≡ y [MOD p]) ↔
      ∀ M > 0, ∃ n, lucasFibonacciSum n ≡ y [MOD M] := by
  constructor
  · intro h
    apply CongruenceClosure.closure_of_eleven_and_diagonal (h 11 (by decide))
    by_contra hn
    obtain ⟨r,hM,hr,hclass⟩ := prime_obstruction_progression y hn
    obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_modEq 11 hM.ne' hr
    obtain ⟨n,hn⟩ := h p hp
    exact hclass p hp he n hn
  · intro h p hp
    exact h _ hp.pos

/-- The exact range surviving every prime modulus, including the surplus at negative odd indices. -/
theorem prime_moduli_iff_upper_or_odd_lower (y : ℕ) :
    (∀ p : ℕ, p.Prime → ∃ n, lucasFibonacciSum n ≡ y [MOD p]) ↔
      (∃ n, y=lucasFibonacciSum n) ∨ CongruenceClosure.OddLowerValue y :=
  (prime_moduli_iff_all y).trans (CongruenceClosure.upper_modular_closure y)

#print axioms prime_obstruction_progression
#print axioms prime_moduli_iff_all
#print axioms prime_moduli_iff_upper_or_odd_lower

end PrimeObstruction
end Arxiv.«2211.10788»
