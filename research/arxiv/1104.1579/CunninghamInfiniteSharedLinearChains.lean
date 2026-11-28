import CunninghamBalancedEnergy
import CunninghamReciprocalUnitFactors
import CunninghamLinearCyclotomicFactors
import CunninghamSharedPrimePowerPrefixes

/-! Infinite polynomial Cunningham chains of both kinds from one common linear seed. -/

namespace CunninghamChain.LinearRoots
open Polynomial CoefficientEnergy

set_option maxRecDepth 4096 in
/-- A multiplier with small tail energy rules out any nonconstant unit-leading
factor. The other input forces such a factor in every integral splitting. -/
theorem balanced_irreducible_of_factor_energy {a : ℕ} (ha : 4 ≤ a) (k : Bool) (n : ℕ)
    (leading : n ≠ 0 → ∀ A B : ℤ[X], polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n=A*B →
      IsUnit A.leadingCoeff ∨ IsUnit B.leadingCoeff)
    (weight : n ≠ 0 → ∃ W : ℤ[X], W ≠ 0 ∧
      let H := polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n * W
      4*energy H H.natDegree < H.leadingCoeff^2) :
    Irreducible (term k a (-(a:ℤ)) n) := by
  let seed : ℤ[X] := C (a:ℤ)*X+C (-(a:ℤ))
  let T := polynomialTerm k seed n
  have a0 : (a:ℤ)≠0 := by omega
  have ds : seed.natDegree=1 := natDegree_linear a0
  have dt : T.natDegree=1+n := (polynomialTerm_shape k seed (by omega) n).1.trans (by rw [ds])
  have tn : T≠0 := by intro h; simp [h] at dt; omega
  change Irreducible (T.map (Int.castRingHom ℚ))
  by_cases zero : n=0
  · apply irreducible_of_degree_eq_one
    change (T.map (Int.castRingHom ℚ)).degree = ((1:ℕ):WithBot ℕ)
    rw [degree_eq_iff_natDegree_eq_of_pos (by decide : 0<1),natDegree_map_eq_of_injective Int.cast_injective]
    omega
  have ct : IsUnit (T.coeff 0) := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero zero
    dsimp [T]
    rw [hi]
    cases k <;> simp [polynomialTerm]
  have primitive : T.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun c hc =>
    isUnit_of_dvd_unit ((C_dvd_iff_dvd_coeff ..).mp hc 0) ct
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast primitive).mp
  refine ⟨fun h => by have := natDegree_eq_zero_of_isUnit h; omega,?_⟩
  have factor (A B : ℤ[X]) (hab : T=A*B) (hu : IsUnit A.leadingCoeff) : IsUnit A := by
    have hconst : IsUnit (A.coeff 0) := by
      rw [hab,mul_coeff_zero] at ct
      exact isUnit_of_mul_isUnit_left ct
    by_cases hA : A.natDegree=0
    · rw [eq_C_of_natDegree_eq_zero hA]
      exact isUnit_C.mpr hconst
    have hB : B≠0 := by rintro rfl; simp [hab] at tn
    obtain ⟨W,wn,small⟩ := weight zero
    change 4*energy (T*W) (T*W).natDegree < (T*W).leadingCoeff^2 at small
    rw [hab,mul_assoc] at small
    have symm := reciprocal_of_small_tail A (B*W) (mul_ne_zero hB wn) hu hconst small
    exact False.elim (no_reciprocal_unit_factor (a:=a) ha k
      (by omega : 0<n) (by omega : 0<A.natDegree) hu hconst ⟨B,hab⟩ symm)
  intro A B hab
  rcases leading zero A B hab with h|h
  · exact Or.inl (factor A B hab h)
  · exact Or.inr (factor B A (hab.trans (mul_comm _ _)) h)

/-- For every prime raised to an odd exponent with coefficient at least 615, both signs
give irreducible rational polynomials at every index from the same seed a(X−1). -/
theorem infinite_shared_odd_power_chains {p : ℕ} (hp : p.Prime) (r : ℕ)
    (ha : 615 ≤ p^(2*r+1)) (k : Bool) (n : ℕ) :
    Irreducible (term k (p^(2*r+1):ℕ) (-(p^(2*r+1):ℕ):ℤ) n) := by
  apply balanced_irreducible_of_factor_energy (by omega) k n
  · exact fun hn A B => odd_prime_power_factor_leading hp r k hn A B
  · intro _
    have kn : multiplier≠0 := by intro he; have := multiplier_shape.2; simp [he] at this
    exact ⟨(X-1)*multiplier,mul_ne_zero (by simpa using X_sub_C_ne_zero (1:ℤ)) kn,
      balanced_tail_energy k ha n⟩

/-- A concrete common seed is 2048(X−1), with 2048=2^11. -/
theorem both_infinite_at_2048 (k : Bool) (n : ℕ) :
    Irreducible (term k 2048 (-2048) n) :=
  infinite_shared_odd_power_chains (p:=2) (by decide) 5 (by decide) k n

/-- Among all integral linear seeds aX+b of positive leading coefficient,
simultaneously infinite chains require b=−a and a≥2. -/
theorem infinite_shared_seed_necessary {a b : ℤ} (ha : 0<a)
    (h : ∀ (k : Bool) (n : ℕ), Irreducible (term k a b n)) : 2≤a ∧ b= -a := by
  have degree (k : Bool) (n : ℕ) : (term k a b n).natDegree=1+n := by
    have d : (C a*X+C b).natDegree=1 := natDegree_linear ha.ne'
    rw [term,natDegree_map_eq_of_injective Int.cast_injective,
      (polynomialTerm_shape k _ (by omega) n).1,d]
  have exclude (k : Bool) (n m : ℕ) (hm : 0 < m) (lt : m.totient < 1+n) :
      ¬ cyclotomic m ℚ ∣ term k a b n := by
    intro dvd
    have assoc := (cyclotomic.irreducible_rat hm).associated_of_dvd (h k n) dvd
    have eq := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated assoc)
    rw [degree,natDegree_cyclotomic] at eq
    omega
  have zero : a+b=0 := by
    by_contra bad
    rcases lt_or_gt_of_ne bad with neg|pos
    · let n := (-(a+b)).toNat
      have he : (n:ℤ)= -(a+b) := Int.toNat_of_nonneg (by omega)
      apply exclude true n 1 (by decide) (by simp; omega)
      exact (linear_cyclotomic_endpoints ..).1.mpr (by simp [sign]; omega)
    · let n := (a+b).toNat
      have he : (n:ℤ)=a+b := Int.toNat_of_nonneg (by omega)
      apply exclude false n 1 (by decide) (by simp; omega)
      exact (linear_cyclotomic_endpoints ..).1.mpr (by simp [sign]; omega)
  refine ⟨?_,by omega⟩
  by_contra! bad
  obtain rfl : a=1 := by omega
  obtain rfl : b= -1 := by omega
  exact exclude true 7 6 (by decide) (by decide)
    ((higher_cyclotomic_iff (a:=1) (b:= -1) (k:=true) (by decide) 7 6 (by decide)).mpr (by decide))

#print axioms balanced_irreducible_of_factor_energy
#print axioms infinite_shared_seed_necessary
#print axioms infinite_shared_odd_power_chains
#print axioms both_infinite_at_2048

end CunninghamChain.LinearRoots
