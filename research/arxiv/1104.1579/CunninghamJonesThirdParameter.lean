import CunninghamJonesReflectedFactors
import CunninghamJonesEightySixCertificate

/-! Jones's third polynomial parameter, corresponding to k = 4 and k = 5. -/

namespace CunninghamChain
open Polynomial JonesEndpointSearch JonesReflection
open scoped Polynomial

/-- Over the rationals, Xʲ + ⋯ + X + 86 is reducible exactly at j = 7 among
positive degrees. This settles the third parameter of Jones's Conjecture 4.1. -/
theorem jones_third_parameter_irreducible_iff (j : ℕ) (hj : 0 < j) :
    Irreducible ((jonesSumPolynomial 86 j).map (Int.castRingHom ℚ)) ↔ j ≠ 7 := by
  have ho : Odd (7 : ℕ) := by decide
  have hp : IsPrimePow ((2^7+1)/3 : ℕ) := (by decide : Nat.Prime 43).isPrimePow
  constructor
  · rintro h rfl
    exact ((jones_prime_power_part_range 7 7 (by decide) ho hp (by decide)
      (Or.inl (by decide))).mp h) rfl
  · intro hne
    by_contra hred
    have hm := jones_prime_power_part_degree_class (by decide : 5≤7) ho hp hj hred
    have hmod : j % 56 = 7 := by simpa [Nat.ModEq] using hm
    obtain ⟨a,b,ha,hb,hab,_,ha₀,hb₀⟩ := jones_factor_two_of_prime_power (q := 43) hp hj hred
    obtain ⟨g, hd, h₀, h₁, he, hc⟩ := reflected_witness ha hb hab
    rw [ha₀] at h₀
    rw [hb₀] at h₁
    exact no_reflected_witness eightySix (by decide) (by decide) eighty_six_certificate
      (j := j) ⟨j/2, by omega⟩ (show (j+1) % 56 = 8 by omega) hne g hd h₀ h₁ he hc

#print axioms jones_third_parameter_irreducible_iff

end CunninghamChain
