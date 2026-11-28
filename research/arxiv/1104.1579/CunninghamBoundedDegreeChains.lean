import CunninghamBalancedFactorCutoff
import CunninghamSharedPrimePowerPrefixes

/-! Uniform bounded-degree exclusion along both entire polynomial Cunningham chains. -/

namespace CunninghamChain.FactorDegree
open Polynomial LinearRoots

private lemma prefix_covers_cutoff (C a : ℕ) (ha : 2^(32*(C+1)) ≤ a) :
    ∃ s : ℕ, 2*16^s < a ∧ C*(Nat.log 2 (4*a+1)+1) ≤ 4*s^2*4^s := by
  let b := Nat.log 2 a
  let s := b/8
  have ha0 : a≠0 := by
    have : 0 < 2^(32*(C+1)) := by positivity
    omega
  have hb : 32*(C+1) ≤ b := (Nat.le_log_iff_pow_le (by decide : 1<2) ha0).mpr ha
  have hs : 4*(C+1) ≤ s := by dsimp [s]; omega
  have hsmall : 4*s+1 < b := by dsimp [s]; omega
  have hlarge : b ≤ 8*s+7 := by dsimp [s]; omega
  have ha' : a < 2^(b+1) := Nat.lt_pow_succ_log_self (by decide : 1<2) _
  have hbit : Nat.log 2 (4*a+1) < b+3 := by
    apply (Nat.log_lt_iff_lt_pow (by decide : 1<2) (by omega)).mpr
    rw [show b+3=(b+1)+2 by omega,pow_add]
    omega
  refine ⟨s,?_,?_⟩
  · calc 2*16^s = 2^(4*s+1) := by rw [pow_succ,pow_mul]; norm_num; omega
         _ < 2^b := Nat.pow_lt_pow_right (by decide) hsmall
         _ ≤ a := Nat.pow_log_le_self _ ha0
  · have h1 : C*(Nat.log 2 (4*a+1)+1) ≤ C*(8*s+10) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : C*(8*s+10) ≤ 4*s^2 := by
      nlinarith [Nat.mul_le_mul_right (8*s+10) hs, Nat.mul_le_mul_left s hs]
    exact h1.trans (h2.trans (Nat.le_mul_of_pos_right _ (by positivity)))

/-- One threshold works for every prime and every odd exponent. At every index
of either chain the iterate is irreducible, or every nonconstant rational factor
has degree larger than the prescribed bound. -/
theorem uniform_odd_prime_power_factor_degrees (D : ℕ) :
    ∃ B : ℕ, ∀ (p : ℕ), p.Prime → ∀ r : ℕ, B ≤ p^(2*r+1) → ∀ (k : Bool) (n : ℕ),
      let a := p^(2*r+1)
      Irreducible (term k a (-a) n) ∨
        ∀ g : ℚ[X], g ∣ term k a (-a) n → 0<g.natDegree → D<g.natDegree := by
  obtain ⟨C,cut⟩ := bounded_factor_index D
  refine ⟨2^(32*(C+1)),?_⟩
  intro p hp r hB k n
  let a := p^(2*r+1)
  have ha : 2≤a := by
    calc 2 ≤ p := hp.two_le
         _ = p^1 := by simp
         _ ≤ a := Nat.pow_le_pow_right hp.pos (by omega : 1≤2*r+1)
  obtain ⟨s,size,cover⟩ := prefix_covers_cutoff C a hB
  by_cases early : n≤4*s^2*4^s
  · exact Or.inl (shared_odd_prime_power_prefix hp r s size k n early)
  · right
    intro g hg hd
    by_contra! small
    exact early ((cut a ha k n (by omega) g hg hd small).trans cover)

#print axioms uniform_odd_prime_power_factor_degrees

end CunninghamChain.FactorDegree
