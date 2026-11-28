import CunninghamPolynomialLengths
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! An integral polynomial test on the roots of a polynomial with constrained leading coefficients. -/

namespace CunninghamChain
open Polynomial

private lemma norm_root_test_product {s : Multiset ℂ} (hne : s ≠ 0)
    (h : ∀ v ∈ s, 0<‖v‖ ∧ ‖v‖<1) : 0<‖s.prod‖ ∧ ‖s.prod‖<1 := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons z s ih =>
    have hz := h z (Multiset.mem_cons_self ..)
    by_cases he : s=0
    · simpa [he] using hz
    obtain ⟨hp,hl⟩ := ih he (fun v hv => h v (Multiset.mem_cons_of_mem hv))
    rw [Multiset.prod_cons,norm_mul]
    exact ⟨mul_pos hz.1 hp,(mul_le_of_le_one_right (norm_nonneg _) hl.le).trans_lt hz.2⟩

/-- An integral test polynomial cannot take values of absolute value strictly between
zero and one at every root of a nonconstant factor with unit leading coefficient. -/
theorem irreducible_of_unit_leading_factor_root_test (f g : ℤ[X]) (hd : 0<f.natDegree)
    (hu : IsUnit (f.coeff 0))
    (hsplit : ∀ a b : ℤ[X], f=a*b → IsUnit a.leadingCoeff ∨ IsUnit b.leadingCoeff)
    (hroot : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z →
      0<‖(g.map (Int.castRingHom ℂ)).eval z‖ ∧ ‖(g.map (Int.castRingHom ℂ)).eval z‖<1) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  classical
  have hprim : f.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun r h =>
    isUnit_of_dvd_unit ((C_dvd_iff_dvd_coeff _ _).mp h 0) hu
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
  refine ⟨fun h => by have := natDegree_eq_zero_of_isUnit h; omega,?_⟩
  have factor (a b : ℤ[X]) (hab : f=a*b) (ha : IsUnit a.leadingCoeff) : IsUnit a := by
    by_cases he : a.natDegree=0
    · have h0 := hu
      rw [hab,mul_coeff_zero] at h0
      rw [eq_C_of_natDegree_eq_zero he]
      exact isUnit_C.mpr (isUnit_of_mul_isUnit_left h0)
    let F := a.map (Int.castRingHom ℂ)
    let G := g.map (Int.castRingHom ℂ)
    have hdF : F.natDegree=a.natDegree := natDegree_map_eq_of_injective Int.cast_injective _
    have hn : F.roots≠0 := by
      intro h
      have := (IsAlgClosed.splits F).natDegree_eq_card_roots
      simp [h,hdF] at this
      contradiction
    have hle : ‖F.leadingCoeff‖=1 := by
      dsimp [F]
      rw [leadingCoeff_map_of_injective Int.cast_injective]
      rcases Int.isUnit_iff.mp ha with e|e <;> simp [e]
    have hvals : ∀ v ∈ F.roots.map G.eval, 0<‖v‖ ∧ ‖v‖<1 := by
      intro v hv
      obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hv
      apply hroot
      rw [hab,Polynomial.map_mul]
      change _=0
      rw [eval_mul,show (a.map (Int.castRingHom ℂ)).eval z=0 from isRoot_of_mem_roots hz,zero_mul]
    obtain ⟨hpos,hsmall⟩ := norm_root_test_product (by simpa using hn) hvals
    let R : ℤ := resultant a g a.natDegree g.natDegree
    have hres : (R:ℂ) = F.leadingCoeff^g.natDegree*(F.roots.map G.eval).prod := by
      have hh := resultant_eq_prod_eval F G g.natDegree (natDegree_map_le) (IsAlgClosed.splits F)
      rw [hdF] at hh
      simpa [R,F,G] using hh
    have hnorm := congrArg (fun w : ℂ => ‖w‖) hres
    rw [norm_mul,norm_pow,hle,one_pow,one_mul,Complex.norm_intCast,←Int.cast_abs] at hnorm
    rw [←hnorm] at hpos hsmall
    have hz : (0 : ℤ) < |R| := by exact_mod_cast hpos
    have h1 : |R| < (1 : ℤ) := by exact_mod_cast hsmall
    omega
  intro a b hab
  rcases hsplit a b hab with ha|hb
  · exact Or.inl (factor a b hab ha)
  · exact Or.inr (factor b a (hab.trans (mul_comm _ _)) hb)

/-- An irreducible leading coefficient forces the unit-leading factor required by the root test. -/
theorem irreducible_of_prime_leading_root_test (f g : ℤ[X]) (hd : 0<f.natDegree)
    (hu : IsUnit (f.coeff 0)) (hp : Irreducible f.leadingCoeff)
    (hroot : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z →
      0<‖(g.map (Int.castRingHom ℂ)).eval z‖ ∧ ‖(g.map (Int.castRingHom ℂ)).eval z‖<1) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  apply irreducible_of_unit_leading_factor_root_test f g hd hu _ hroot
  intro a b hab
  apply hp.isUnit_or_isUnit
  rw [hab,leadingCoeff_mul]

#print axioms irreducible_of_unit_leading_factor_root_test
#print axioms irreducible_of_prime_leading_root_test

end CunninghamChain
