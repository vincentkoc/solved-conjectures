import HosoyaFourCharacterObstruction
import LucasFibonacciPellPrimeMass
import LucasFibonacciPrimeModulusClosure

/-! Every candidate missing the bilateral range is excluded by positive prime mass. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Filter Topology CunninghamChain.PrimeMass

/-- All prime moduli whose complete upper orbit misses y. -/
def missingPrimeModuli (y : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∀ n : ℕ, ¬lucasFibonacciSum n ≡ y [MOD p]}

private theorem eleven_nonzero {y : ℕ} (ha : IsSquare (5*(y:ℤ)^2+44)) : (y:ZMod 11)≠0 := by
  rintro hy
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff ..).mp hy
  obtain ⟨v,hv⟩ := ha
  have e := congrArg (fun z : ℤ => (z:ZMod 121)) hv
  rw [hk] at e
  push_cast at e
  have zero : (5:ZMod 121)*11^2=0 := by decide
  have ns : ∀ t : ZMod 121, t*t≠44 := by decide +kernel
  apply ns v
  linear_combination -e + (k:ZMod 121)^2*zero

private theorem discriminant_data (y : ℕ) (hfive : y≠5) (ha : IsSquare (5*(y:ℤ)^2+44)) :
    ¬IsSquare (5*(y:ℤ)^2-44).natAbs ∧ (5*(y:ℤ)^2-44).natAbs.Coprime 55 := by
  let b := 5*(y:ℤ)^2-44
  refine ⟨?_,?_⟩
  · by_cases hs : y<3
    · interval_cases y <;> norm_num
    · have h3 : (3:ℤ)≤y := by exact_mod_cast (by omega : 3≤y)
      have hpos : 0≤b := by dsimp [b]; nlinarith [mul_nonneg (sub_nonneg.mpr h3) (show 0≤(y:ℤ)+3 by omega)]
      rintro ⟨v,hv⟩
      have he : (b.natAbs:ℤ)=(v:ℤ)*v := by exact_mod_cast hv
      rw [Int.natCast_natAbs,abs_of_nonneg hpos] at he
      exact hfive ((pell_product_square_iff y).mp (ha.mul ⟨v,he⟩))
  · let : Fact (Nat.Prime 11) := ⟨by decide⟩
    have cop (p : ℕ) (hp : p.Prime) (hn : (b:ZMod p)≠0) : b.natAbs.Coprime p := by
      apply Nat.Coprime.symm
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      exact hn ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.natAbs_dvd_natAbs.mp (by simpa using hd)))
    change b.natAbs.Coprime (5*11)
    apply Nat.Coprime.mul_right
    · apply cop _ (by decide)
      dsimp [b]; push_cast; rw [show (5:ZMod 5)=0 by decide]; simp; decide
    · apply cop _ (by decide)
      dsimp [b]; push_cast; rw [show (44:ZMod 11)=0 by decide,sub_zero]
      exact mul_ne_zero (by decide) (pow_ne_zero _ (eleven_nonzero ha))

private theorem even_lower_missing_mass (j : ℕ) (hfive : lowerNeighborAtAddTwo (2*j)≠5)
    {c : ℝ} (hc : c<1/16) :
    ∀ᶠ x : ℝ in 𝓝[>] 1, c<(x-1)*mass (missingPrimeModuli (lowerNeighborAtAddTwo (2*j))) x := by
  let y := lowerNeighborAtAddTwo (2*j)
  let b := 5*(y:ℤ)^2-44
  obtain ⟨h₁,h₂⟩ := discriminant_data y hfive (even_lower_positive_square j)
  obtain ⟨P,hlim,hP⟩ := four_sign_prime_mass b h₁ h₂
  filter_upwards [hlim.eventually_const_lt hc,self_mem_nhdsWithin] with x hx h1
  apply hx.trans_le
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (le_of_lt h1))
  apply (summable_weight P h1).tsum_le_tsum _ (summable_weight _ h1)
  intro p
  apply div_le_div_of_nonneg_right _ (by positivity)
  by_cases hp : p.Prime ∧ p∈P
  · obtain ⟨hB,h₁₁,h₅,hm⟩ := hP p hp.2 hp.1
    have han : p∈missingPrimeModuli y := ⟨hp.1,even_lower_prime_obstruction hp.1 j h₅ hm h₁₁
      (by simpa [b,y] using hB)⟩
    simp [weight,hp.1,hp.2,han,y] at *
  · rw [weight,if_neg hp]; exact weight_nonneg _ p

/-- Every value outside the upper and positive odd lower ranges has a uniform lower
bound of one sixteenth for the normalized mass of prime moduli missing it. -/
theorem missing_prime_mass_uniform (y : ℕ)
    (hy : ¬((∃ n, y=lucasFibonacciSum n) ∨ CongruenceClosure.OddLowerValue y))
    {c : ℝ} (hc : c<1/16) :
    ∀ᶠ x : ℝ in 𝓝[>] 1, c<(x-1)*mass (missingPrimeModuli y) x := by
  by_cases h : (∃ n, y=lucasFibonacciSum n) ∨ IsLowerNeighborValue y
  · rcases h with hu | hl
    · exact (hy (Or.inl hu)).elim
    rcases hl with h3 | ⟨m,hm⟩
    · exact (hy (Or.inr (Or.inl h3))).elim
    rcases Nat.even_or_odd m with ⟨j,hj⟩ | ⟨j,hj⟩
    · rw [show m=2*j by omega] at hm
      rw [hm] at hy ⊢
      apply even_lower_missing_mass j _ hc
      intro he
      exact hy (Or.inl ⟨2,he.trans (by decide)⟩)
    · exact (hy (Or.inr (Or.inr ⟨j,by rwa [show 2*j+1=m by omega]⟩))).elim
  · exact missing_prime_mass_lower y h (c:=c) (by linarith)

/-- The missing prime moduli are infinite for every candidate outside the congruence closure. -/
theorem infinite_missing_prime_moduli (y : ℕ)
    (hy : ¬((∃ n, y=lucasFibonacciSum n) ∨ CongruenceClosure.OddLowerValue y)) :
    (missingPrimeModuli y).Infinite := by
  intro hf
  have lo := missing_prime_mass_uniform y hy (c:=1/32) (by norm_num)
  have hi := (finite_mass_tendsto hf).eventually_lt_const (by norm_num : (0:ℝ)<1/32)
  obtain ⟨x,hx,hx'⟩ := (lo.and hi).exists
  exact (lt_asymm hx hx')

/-- Removing any finite set of primes from the modular tests preserves exactly the upper
values and the positive odd lower values. -/
theorem cofinite_prime_tests (y : ℕ) (T : Set ℕ) (hT : T.Finite) :
    (∀ p : ℕ, p.Prime → p∉T → ∃ n, lucasFibonacciSum n ≡ y [MOD p]) ↔
      (∃ n, y=lucasFibonacciSum n) ∨ CongruenceClosure.OddLowerValue y := by
  constructor
  · intro h
    by_contra hy
    apply infinite_missing_prime_moduli y hy
    apply hT.subset
    intro p hp
    by_contra hn
    obtain ⟨n,he⟩ := h p hp.1 hn
    exact hp.2 n he
  · intro hy p hp _
    exact (prime_moduli_iff_upper_or_odd_lower y).mpr hy p hp

#print axioms missing_prime_mass_uniform
#print axioms infinite_missing_prime_moduli
#print axioms cofinite_prime_tests

end Arxiv.«2211.10788».PrimeObstruction
