import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Tactic

/-! Arithmetic of nonnegative real polynomial factors of a binary polynomial. -/

open Polynomial Finset
open scoped Polynomial

namespace Green28PolynomialReduction

/-- Every coefficient, including coefficients beyond the degree, is zero or one. -/
def Binary (p : ℝ[X]) : Prop := ∀ n, p.coeff n=0 ∨ p.coeff n=1

private lemma integer_model {p : ℝ[X]} (h : Binary p) :
    ∃ P : ℤ[X], P.map (algebraMap ℤ ℝ)=p := by
  apply (Polynomial.mem_lifts (f := algebraMap ℤ ℝ) p).mp
  apply (Polynomial.lifts_iff_coeff_lifts (f := algebraMap ℤ ℝ) p).mpr
  intro n
  rcases h n with he|he
  · exact ⟨0,by simp [he]⟩
  · exact ⟨1,by simp [he]⟩

/-- Each coefficient of a monic real divisor of a monic binary polynomial
is an algebraic integer. -/
theorem integral_coefficient {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (binary : Binary (f*g)) (n : ℕ) : IsIntegral ℤ (f.coeff n) := by
  obtain ⟨P,hP⟩ := integer_model binary
  have hmon : P.Monic := monic_of_injective (Int.cast_injective (α := ℝ)) (by rw [hP]; exact hf.mul hg)
  exact isIntegral_coeff_of_dvd P f hmon hf (by rw [hP]; exact dvd_mul_right f g) n

/-- A monic cofactor bounds every coefficient of a nonnegative factor by one. -/
theorem coeff_le_one {f g : ℝ[X]} (hg : g.Monic)
    (fpos : ∀ i, 0 ≤ f.coeff i) (gpos : ∀ i, 0 ≤ g.coeff i)
    (binary : Binary (f*g)) (n : ℕ) : f.coeff n ≤ 1 := by
  have one := binary (n+g.natDegree)
  have term : f.coeff n*g.coeff g.natDegree ≤ (f*g).coeff (n+g.natDegree) := by
    rw [coeff_mul]
    exact single_le_sum (f := fun x : ℕ×ℕ => f.coeff x.1*g.coeff x.2)
      (fun x _ => mul_nonneg (fpos x.1) (gpos x.2)) (show (n,g.natDegree) ∈ antidiagonal (n+g.natDegree) from mem_antidiagonal.mpr rfl)
  rw [hg.coeff_natDegree,mul_one] at term
  rcases one with e|e <;> linarith only [e,term]

/-- A rational coefficient in either monic nonnegative factor already belongs
to the binary alphabet, even when the other coefficients are arbitrary reals. -/
theorem rational_coefficient {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (fpos : ∀ i, 0≤f.coeff i) (gpos : ∀ i, 0≤g.coeff i)
    (binary : Binary (f*g)) (n : ℕ) (q : ℚ) (hq : (q:ℝ)=f.coeff n) :
    f.coeff n=0 ∨ f.coeff n=1 := by
  have hi := integral_coefficient hf hg binary n
  rw [←hq] at hi
  have hiq : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (B := ℝ) (algebraMap ℚ ℝ).injective).mp hi
  obtain ⟨z,hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hiq
  have e : (z:ℝ)=f.coeff n := by
    rw [←hq,←hz]
    norm_num
  have lo := fpos n
  have high := coeff_le_one hg fpos gpos binary n
  rw [←e] at lo high ⊢
  have l : 0≤z := by exact_mod_cast lo
  have u : z≤1 := by exact_mod_cast high
  interval_cases z <;> norm_num

/-- Monic division recovers the other factor over any real subring containing
the coefficients of the first. No positivity hypothesis is needed here. -/
theorem coeff_mem_of_monic_factor {f g : ℝ[X]} (fm : f.Monic) (bin : Binary (f*g))
    (S : Subring ℝ) (hf : ∀ i, f.coeff i ∈ S) (j : ℕ) : g.coeff j ∈ S := by
  have lift (p : ℝ[X]) (h : ∀ i, p.coeff i ∈ S) : ∃ P : S[X], P.map S.subtype = p := by
    apply (Polynomial.mem_lifts p).mp
    exact (Polynomial.lifts_iff_coeff_lifts p).mpr (fun i => ⟨⟨_,h i⟩,rfl⟩)
  obtain ⟨F,eqF⟩ := lift f hf
  obtain ⟨D,eqD⟩ := lift (f*g) (fun i => by
    rcases bin i with he|he
    · rw [he]; exact S.zero_mem
    · rw [he]; exact S.one_mem)
  have mon : F.Monic := monic_of_injective (f := S.subtype) Subtype.val_injective (eqF ▸ fm)
  have e : (D /ₘ F).map S.subtype = g := by
    rw [map_divByMonic _ mon,eqD,eqF,mul_divByMonic_cancel_left _ fm]
  rw [← e, coeff_map]
  exact ((D /ₘ F).coeff j).property

/-- If all coefficients of one factor are rational, both factors are binary. -/
theorem rational_factor {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (fpos : ∀ i, 0≤f.coeff i) (gpos : ∀ i, 0≤g.coeff i)
    (binary : Binary (f*g)) (rat : ∀ i, ∃ q : ℚ, (q:ℝ)=f.coeff i) :
    Binary f ∧ Binary g := by
  have fb : Binary f := by
    intro i; obtain ⟨q,e⟩ := rat i
    exact rational_coefficient hf hg fpos gpos binary i q e
  obtain ⟨F,hF⟩ := integer_model fb
  obtain ⟨P,hP⟩ := integer_model binary
  have mon : F.Monic := monic_of_injective (Int.cast_injective (α := ℝ)) (by rw [hF]; exact hf)
  have eq : (P /ₘ F).map (algebraMap ℤ ℝ)=g := by
    rw [map_divByMonic _ mon,hP,hF,mul_divByMonic_cancel_left _ hf]
  refine ⟨fb,fun i => ?_⟩
  apply rational_coefficient hg hf gpos fpos (mul_comm f g ▸ binary) i ((P /ₘ F).coeff i : ℚ)
  simpa using congrArg (fun p : ℝ[X] => p.coeff i) eq

#print axioms coeff_mem_of_monic_factor
#print axioms coeff_le_one
#print axioms integral_coefficient
#print axioms rational_coefficient
#print axioms rational_factor

end Green28PolynomialReduction
