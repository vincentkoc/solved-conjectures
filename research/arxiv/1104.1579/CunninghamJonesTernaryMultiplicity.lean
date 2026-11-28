import CunninghamJonesTranslatedCoefficients

/-! The multiplicity at 1 of each reduced factor at a high power of three. -/

namespace CunninghamChain.JonesMultiplicity
open Polynomial
open scoped Polynomial

private lemma unique_first {m : ℤ} {A : ℤ[X]} {e f : ℕ}
    (he : FirstCoefficientMod m A e) (hf : FirstCoefficientMod m A f) : e=f := by
  rcases lt_trichotomy e f with h|h|h
  · exact False.elim (he.2 (hf.1 e h))
  · exact h
  · exact False.elim (hf.2 (he.1 f h))

private lemma first_at_root (A : ℤ[X]) (ha : A.Monic) :
    FirstCoefficientMod 3 (A.comp (X+1)) ((A.map (Int.castRingHom (ZMod 3))).rootMultiplicity 1) := by
  let φ := Int.castRingHom (ZMod 3)
  let V := (A.comp (X+1)).map φ
  have eq : V=(A.map φ).comp (X+C 1) := by simp [V,map_comp]
  have hv : V≠0 := eq ▸ comp_X_add_C_ne_zero_iff.mpr (ha.map φ).ne_zero
  have e : (A.map φ).rootMultiplicity 1=V.natTrailingDegree := by rw [eq,rootMultiplicity_eq_natTrailingDegree]
  change FirstCoefficientMod 3 (A.comp (X+1)) ((A.map φ).rootMultiplicity 1)
  rw [e]
  have coef (i : ℕ) : V.coeff i=(((A.comp (X+1)).coeff i:ℤ):ZMod 3) := by simp [V,φ,coeff_map]
  constructor
  · intro i hi
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ((coef i).symm.trans (coeff_eq_zero_of_lt_natTrailingDegree hi))
  · intro hd
    apply trailingCoeff_nonzero_iff_nonzero.mpr hv
    exact (coef _).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd)

private lemma translated_zero (m j : ℕ) :
    ((jonesSumPolynomial m j).comp (X+1)).coeff 0=((m+j:ℕ):ℤ) := by
  rw [coeff_zero_eq_eval_zero,eval_comp]
  simp [jonesSumPolynomial,eval_finsetSum]

/-- If 9 divides m exactly to the second 3-adic level, a degree divisible
by 27 leaves only four possible multiplicities at 1 in each factor modulo 3. -/
theorem jones_factor_ternary_multiplicity {m d : ℕ} (hm : 9 ∣ m) (hm' : ¬27 ∣ m)
    (hd : ¬3 ∣ d) (n : ℕ) {A B : ℤ[X]} (ha : A.Monic) (hb : B.Monic)
    (hab : A*B=jonesSumPolynomial m (3^(n+3)*d)) :
    let e := (A.map (Int.castRingHom (ZMod 3))).rootMultiplicity 1
    let h := 3^(n+2)
    e=0 ∨ e=h-1 ∨ e=2*h ∨ e=3*h-1 := by
  let φ := Int.castRingHom (ZMod 3)
  let e := (A.map φ).rootMultiplicity 1
  let f := (B.map φ).rootMultiplicity 1
  let h := 3^(n+2)
  change e=0 ∨ e=h-1 ∨ e=2*h ∨ e=3*h-1
  have poweq : 3^(n+3)=3*h := pow_succ' 3 (n+2)
  have pos : 0<h := by dsimp [h]; positivity
  obtain ⟨ht₃,ht₉⟩ := jones_translated_first_coefficients hm hd (n+2)
  rw [←hab] at ht₃ ht₉
  have total := unique_first (first_at_root (A*B) (ha.mul hb)) ht₃
  rw [Polynomial.map_mul,rootMultiplicity_mul (mul_ne_zero (ha.map φ).ne_zero (hb.map φ).ne_zero)] at total
  change e+f=3^(n+3)-1 at total
  rw [poweq] at total
  by_cases h₁ : e=0
  · exact Or.inl h₁
  by_cases h₂ : f=0
  · exact Or.inr (Or.inr (Or.inr (by omega)))
  have mc : ¬(3:ℤ)^3 ∣ ((A.comp (X+1))*(B.comp (X+1))).coeff 0 := by
    rw [←mul_comp,hab,translated_zero]
    intro hsum
    have hsum' := (Int.natCast_dvd_natCast).mp (show (27:ℤ) ∣ _ from hsum)
    have h27 : 27 ∣ 3^(n+3)*d := by rw [pow_add]; exact (dvd_mul_left (3^3) _).trans (dvd_mul_right ..)
    exact hm' ((Nat.dvd_add_left h27).mp hsum')
  rw [mul_comp] at ht₉
  have short := shorter_multiplicity (show Prime (3:ℤ) by norm_num) (first_at_root A ha) (first_at_root B hb)
    ht₉ mc (Nat.pos_of_ne_zero h₁) (Nat.pos_of_ne_zero h₂)
    (show 2*(h-1)<e+f by omega)
  change min e f=h-1 at short
  omega

#print axioms jones_factor_ternary_multiplicity

end CunninghamChain.JonesMultiplicity
