import Green33FiniteQuarticCharacter

/-! Prime-field forms of the finite-field Stepanov bounds. -/

open Finset Polynomial
open scoped BigOperators Polynomial

namespace Green33PrimeQuarticCharacter

variable {K : Type*} [Field K]

theorem stepanov_bound [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {I J r n : ℕ} (f : K[X]) (nf : f≠0) (c : K)
    (points : Finset K) (test : ∀ x∈points, x^p=x+c ∧ f.eval x≠0 ∧ f.eval x^n=1)
    (width : I≤p) (rpos : 0<r) (small : r≤p)
    (gap : I≤(n*f.natTrailingDegree)%p) (room : (n*f.natTrailingDegree)%p+I≤p)
    (more : r*(I+J+r*f.natDegree+1)<2*(J*I)) :
    r*points.card≤J*p+I+n*f.natDegree := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt rpos)
  exact Green33FiniteQuarticCharacter.stepanov_bound (p:=p) (e:=1) (pow_one p).symm
    f nf c points test width small gap room more

#print axioms stepanov_bound

section PrimeValues

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
variable [Algebra (ZMod p) K] [CharP K p]

theorem quartic_character_sum (g : (ZMod p)[X]) (deg : g.natDegree≤4) (a : K)
    (odd : Odd ((g.map (algebraMap (ZMod p) K)).rootMultiplicity a)) (big : 400≤p) :
    |∑ x : ZMod p, quadraticChar (ZMod p) (g.eval x)|≤80*((p.sqrt:ℤ)+1)+4 := by
  have fld : ringChar (ZMod p)≠2 := by rw [Algebra.ringChar_eq (ZMod p) K,ringChar.eq K p];omega
  simpa only [ZMod.card] using Green33FiniteQuarticCharacter.quartic_character_sum fld g deg a odd

#print axioms quartic_character_sum

end PrimeValues

theorem quartic_lower {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] (ext : Odd (Module.finrank (ZMod p) K))
    (g : (ZMod p)[X]) (deg : g.natDegree≤4) (r b : K)
    (nz : b≠0) (witness : (g.map (algebraMap (ZMod p) K)).eval r=b^2)
    (big : 400≤p) :
    -(80*((p.sqrt:ℤ)+1)+4)≤∑ x : ZMod p, quadraticChar (ZMod p) (g.eval x) := by
  have fld : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  simpa only [ZMod.card] using Green33FiniteQuarticCharacter.quartic_lower fld ext g deg r b nz witness

#print axioms quartic_lower

theorem quartic_dichotomy {p : ℕ} [Fact p.Prime] (g : (ZMod p)[X]) (deg : g.natDegree≤4)
    (big : 400≤p) :
    |∑ x : ZMod p, quadraticChar (ZMod p) (g.eval x)|≤80*((p.sqrt:ℤ)+1)+4 ∨
      ∃ c : ZMod p, ∃ q : (ZMod p)[X], g=C c*q^2 := by
  have fld : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  simpa only [ZMod.card] using Green33FiniteQuarticCharacter.quartic_dichotomy fld g deg

#print axioms quartic_dichotomy

end Green33PrimeQuarticCharacter
