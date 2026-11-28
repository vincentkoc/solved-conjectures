import Mathlib

/-! A factor measure estimate from root norms, and the fixed-degree gap above one. -/

namespace CunninghamChain.FactorDegree
open Polynomial

private lemma product_bound (s : Multiset ℂ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ)
    (h : ∀ z ∈ s, (max 1 ‖z‖)^n ≤ B * ‖z‖^n) :
    (s.map (fun z => max 1 ‖z‖)).prod ^ n ≤ B ^ s.card * ‖s.prod‖ ^ n := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have hz := h z (Multiset.mem_cons_self ..)
    have hs := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul, mul_pow,
      pow_succ B]
    calc _ ≤ (B * ‖z‖^n) * (B^s.card * ‖s.prod‖^n) := by
            exact mul_le_mul hz hs (pow_nonneg (Multiset.prod_nonneg (by simp +contextual)) _)
              (by positivity)
         _ = _ := by ring

/-- A uniform bound on the inverse root norms controls Mahler measure relative to
the constant coefficient, with multiplicities retained. -/
theorem mahler_bound_of_root_bound (f : ℂ[X]) {B : ℝ} (hB : 0 ≤ B) (n : ℕ)
    (h : ∀ z ∈ f.roots, (max 1 ‖z‖)^n ≤ B * ‖z‖^n) :
    f.mahlerMeasure^n ≤ B^f.natDegree * ‖f.coeff 0‖^n := by
  have hs := IsAlgClosed.splits f
  have hc := congrArg norm hs.coeff_zero_eq_leadingCoeff_mul_prod_roots
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hc
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hc, mul_pow, mul_pow,
    hs.natDegree_eq_card_roots]
  calc _ ≤ ‖f.leadingCoeff‖^n * (B ^ f.roots.card * ‖f.roots.prod‖^n) :=
          mul_le_mul_of_nonneg_left (product_bound _ hB n h) (by positivity)
       _ = _ := by ring

/-- Northcott finiteness gives one exponent separating every integer polynomial
of bounded degree and Mahler measure greater than one from the interval [1,2). -/
theorem fixed_degree_measure_gap (D : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ f : ℤ[X], f.natDegree ≤ D →
      1 < (f.map (Int.castRingHom ℂ)).mahlerMeasure →
      2 ≤ (f.map (Int.castRingHom ℂ)).mahlerMeasure ^ K := by
  classical
  let M := fun f : ℤ[X] => (f.map (Int.castRingHom ℂ)).mahlerMeasure
  let S := {f : ℤ[X] | f.natDegree ≤ D ∧ M f ≤ 2}
  have fin : S.Finite := by simpa [S,M] using finite_mahlerMeasure_le D 2
  let power := fun f : ℤ[X] => if h : 1 < M f then (pow_unbounded_of_one_lt (2:ℝ) h).choose else 1
  let K := max 1 (fin.toFinset.sup power)
  have hK : 1 ≤ K := le_max_left ..
  refine ⟨K,hK,?_⟩
  intro f deg hm
  change 1 < M f at hm
  change 2 ≤ M f ^ K
  by_cases small : M f ≤ 2
  · have hf : f ∈ fin.toFinset := fin.mem_toFinset.mpr ⟨deg,small⟩
    have hk : power f ≤ K := (Finset.le_sup (f:=power) hf).trans (le_max_right ..)
    have he : 2 < M f ^ power f := by
      simpa [power,hm] using (pow_unbounded_of_one_lt (2:ℝ) hm).choose_spec
    exact he.le.trans (pow_le_pow_right₀ hm.le hk)
  · exact (le_of_not_ge small).trans (by simpa using pow_le_pow_right₀ hm.le hK)

#print axioms mahler_bound_of_root_bound
#print axioms fixed_degree_measure_gap

end CunninghamChain.FactorDegree
