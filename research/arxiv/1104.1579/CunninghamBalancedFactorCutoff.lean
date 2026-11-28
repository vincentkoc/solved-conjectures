import CunninghamFactorMeasureBounds
import CunninghamLinearCyclotomicFactors

/-! A logarithmic bound on the index of a fixed-degree factor of a balanced Jones iterate. -/

namespace CunninghamChain.FactorDegree
open Polynomial LinearRoots
open scoped nonZeroDivisors

private noncomputable abbrev iterate (k : Bool) (a n : ℕ) :=
  polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n

private lemma lift_factor (F : ℤ[X]) (g : ℚ[X]) (hg : g ∣ F.map (Int.castRingHom ℚ)) :
    ∃ f : ℤ[X], f ∣ F ∧ f.natDegree = g.natDegree := by
  let q := IsLocalization.integerNormalization ℤ⁰ g
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec ℤ⁰ g
  have h0 : (b:ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
  have hbq : q.map (Int.castRingHom ℚ) = C (b:ℚ)*g := by
    rw [C_mul']
    exact he
  have hu : IsUnit (C (b:ℚ)) := (isUnit_iff_ne_zero.mpr h0).map C
  have hq := Polynomial.map_dvd (Int.castRingHom ℚ) q.primPart_dvd
  rw [hbq] at hq
  refine ⟨q.primPart,(IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ q.isPrimitive_primPart).mpr
    ((hu.dvd_mul_left.mp hq).trans hg),?_⟩
  rw [q.natDegree_primPart, ←natDegree_map_eq_of_injective (p:=q) (Int.castRingHom ℚ).injective_int,
    hbq,natDegree_C_mul h0]

private lemma root_bound (k : Bool) (a n : ℕ) {z : ℂ}
    (hz : aeval z (term k a (-a) n) = 0) :
    (max 1 ‖z‖)^n ≤ (4*(a:ℝ)+1)*‖z‖^n := by
  by_cases h : 1 ≤ ‖z‖
  · rw [max_eq_right h]
    exact le_mul_of_one_le_left (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) a])
  have hz1 : z ≠ 1 := by rintro rfl; simp at h
  have e := (root_equation k a (-a) n z hz1).mp hz
  have eq : z^n*((a:ℂ)*(z-1)^2+sign k) = sign k := by
    push_cast at e
    linear_combination e
  have eu : ‖(sign k:ℂ)‖=1 := by cases k <;> norm_num [sign]
  have hb : ‖z-1‖ ≤ 2 := (norm_sub_le z 1).trans (by simp; linarith)
  have ht : ‖(a:ℂ)*(z-1)^2+sign k‖ ≤ 4*a+1 := calc
    _ ≤ ‖(a:ℂ)*(z-1)^2‖+‖(sign k:ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul,norm_pow,Complex.norm_natCast,eu]
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (Nat.cast_nonneg a : 0≤(a:ℝ))]
  rw [max_eq_left (le_of_not_ge h),one_pow, mul_comm]
  calc 1 = ‖z‖^n * ‖(a:ℂ)*(z-1)^2+sign k‖ := by
          rw [←norm_pow,←norm_mul,eq,eu]
       _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)

private lemma measure_range {k : Bool} {a n : ℕ} (ha : 2≤a) (hn : 0<n) {f : ℤ[X]}
    (hf : f ∣ iterate k a n) (hd : 0<f.natDegree) :
    let M := (f.map (Int.castRingHom ℂ)).mahlerMeasure
    1 < M ∧ M^n ≤ (4*(a:ℝ)+1)^f.natDegree := by
  have ht : IsUnit ((iterate k a n).coeff 0) := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    cases k <;> simp [iterate,polynomialTerm]
  have cf : IsUnit (f.coeff 0) := by
    apply isUnit_of_dvd_unit _ ht
    obtain ⟨g,hg⟩ := hf
    rw [hg,mul_coeff_zero]
    exact dvd_mul_right ..
  have hne : f≠0 := by rintro rfl; simp at hd
  have cmp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := Subsingleton.elim _ _
  have forbid := (both_signs_cyclotomic_free_iff a (-a) (by omega)).mpr ⟨by omega,rfl⟩
  constructor
  · refine lt_of_le_of_ne (one_le_mahlerMeasure_of_ne_zero hne) ?_
    intro hm
    obtain ⟨d,hd',dv⟩ := cyclotomic_dvd_of_mahlerMeasure_eq_one hm.symm
      (fun h => cf.ne_zero (X_dvd_iff.mp h)) (by
        rw [degree_eq_natDegree hne]
        exact_mod_cast (by omega : f.natDegree≠0))
    apply forbid k n d hn hd'
    simpa only [map_cyclotomic_int, term, iterate] using Polynomial.map_dvd (Int.castRingHom ℚ) (dv.trans hf)
  · let F := f.map (Int.castRingHom ℂ)
    have hc : ‖F.coeff 0‖=1 := by
      rcases Int.isUnit_iff.mp cf with hv|hv <;> simp [F,coeff_map,hv]
    have deg : F.natDegree=f.natDegree := natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int _
    have bound := mahler_bound_of_root_bound F (by positivity : 0≤4*(a:ℝ)+1) n (by
      intro z hz
      apply root_bound
      have atRoot := (isRoot_of_mem_roots hz).dvd (Polynomial.map_dvd (Int.castRingHom ℂ) hf)
      simpa only [term,iterate,aeval_def,eval_map,eval₂_map,cmp,IsRoot.def] using atRoot)
    simpa only [hc,one_pow,mul_one,deg] using bound

/-- The index of every nonconstant rational factor of degree at most D is bounded
by a constant depending only on D times the binary length of 4a+1. -/
theorem bounded_factor_index (D : ℕ) :
    ∃ C : ℕ, ∀ (a : ℕ), 2≤a → ∀ (k : Bool) (n : ℕ), 0<n → ∀ g : ℚ[X],
      g ∣ term k a (-a) n → 0<g.natDegree → g.natDegree≤D →
      n ≤ C*(Nat.log 2 (4*a+1)+1) := by
  obtain ⟨K,_,gap⟩ := fixed_degree_measure_gap D
  refine ⟨D*K,?_⟩
  intro a ha k n hn g hg hgpos hD
  obtain ⟨f,hf,deg⟩ := lift_factor (iterate k a n) g hg
  obtain ⟨lo,hi⟩ := measure_range ha hn hf (deg.trans_gt hgpos)
  let M := (f.map (Int.castRingHom ℂ)).mahlerMeasure
  let b := Nat.log 2 (4*a+1)+1
  have two : (2:ℝ) ≤ M^K := gap f (deg ▸ hD) lo
  have bits : 4*(a:ℝ)+1 ≤ (2:ℝ)^b := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (b:=2) (by decide) (4*a+1)).le
  have hn' : (2:ℝ)^n ≤ (2:ℝ)^(D*K*b) := calc
    _ ≤ (M^K)^n := pow_le_pow_left₀ (by norm_num) two _
    _ = (M^n)^K := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ ≤ ((4*(a:ℝ)+1)^f.natDegree)^K := pow_le_pow_left₀ (pow_nonneg (by linarith : 0 ≤ M) _) hi _
    _ ≤ (((2:ℝ)^b)^D)^K := by
      apply pow_le_pow_left₀ (by positivity)
      exact (pow_le_pow_left₀ (by positivity) bits _).trans
        (pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (deg ▸ hD))
    _ = _ := by rw [←pow_mul,←pow_mul]; congr 1; ring
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hn'

#print axioms bounded_factor_index

end CunninghamChain.FactorDegree
