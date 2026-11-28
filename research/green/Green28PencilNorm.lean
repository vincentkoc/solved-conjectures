import Green28PrimitiveSupport

/-! Rational multiples of a coprime polynomial pencil in an algebraic weight. -/

namespace Green28PencilNorm

open Polynomial Finset Green28AlgebraicWidth
open scoped Polynomial

/-- A rational polynomial pencil specialized at a real parameter. -/
noncomputable def pencil (A B : ℚ[X]) (u : ℝ) : ℝ[X] :=
  A.map (algebraMap ℚ ℝ)+C u*B.map (algebraMap ℚ ℝ)

private theorem pencil_top {A B : ℚ[X]} (am : A.Monic) (small : B.natDegree < A.natDegree) (u : ℝ) :
    (pencil A B u).Monic ∧ (pencil A B u).natDegree = A.natDegree := by
  have less : (C u*B.map (algebraMap ℚ ℝ)).natDegree<(A.map (algebraMap ℚ ℝ)).natDegree :=
    (natDegree_C_mul_le _ _).trans_lt (by simpa only [natDegree_map] using small)
  exact ⟨(am.map _).add_of_left (degree_lt_degree less),
    (natDegree_add_eq_left_of_natDegree_lt less).trans (natDegree_map _)⟩

/-- Every nonzero rational multiple of the specialized pencil has degree at
least the algebraic degree of its parameter times the degree of its leading mask. -/
theorem multiple_degree {A B F : ℚ[X]} (am : A.Monic) (small : B.natDegree < A.natDegree)
    (cop : IsCoprime A B) {u : ℝ} (int : IsIntegral ℚ u) (fn : F ≠ 0)
    (div : pencil A B u ∣ F.map (algebraMap ℚ ℝ)) :
    (minpoly ℚ u).natDegree*A.natDegree ≤ F.natDegree := by
  let F' := F*C F.leadingCoeff⁻¹
  have mon : F'.Monic := monic_mul_leadingCoeff_inv fn
  have divisor : pencil A B u ∣ F'.map (algebraMap ℚ ℝ) := by
    dsimp only [F']; rw [Polynomial.map_mul]; exact div.trans (dvd_mul_right _ _)
  obtain ⟨g,eq⟩ := divisor
  obtain ⟨pm,deg⟩ := pencil_top am small u
  have gm : g.Monic := pm.of_mul_monic_left (eq ▸ mon.map _)
  let d := (minpoly ℚ u).natDegree
  have pos : 0 < d := minpoly.natDegree_pos int
  have lower := cofactor_degree A B F' u g gm cop eq.symm (d-1) (by change d-1 < d; omega)
  have total := congrArg natDegree eq
  rw [natDegree_map,pm.natDegree_mul gm,deg] at total
  have norm : F'.natDegree = F.natDegree := natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr fn))
  change d*A.natDegree ≤ F.natDegree
  calc
    d*A.natDegree = A.natDegree+(d-1)*A.natDegree := by
      conv_lhs => rw [show d = (d-1)+1 by omega,add_mul,one_mul,add_comm]
    _ ≤ A.natDegree+g.natDegree := Nat.add_le_add_left lower _
    _ = F.natDegree := total.symm.trans norm

/-- A monic rational multiple reaching the minimum possible degree
divides every rational multiple of the pencil. -/
theorem least_multiple {A B M F : ℚ[X]} (am : A.Monic) (small : B.natDegree < A.natDegree)
    (cop : IsCoprime A B) {u : ℝ} (int : IsIntegral ℚ u) (mon : M.Monic)
    (bound : M.natDegree ≤ (minpoly ℚ u).natDegree*A.natDegree)
    (hit : pencil A B u ∣ M.map (algebraMap ℚ ℝ)) :
    pencil A B u ∣ F.map (algebraMap ℚ ℝ) ↔ M ∣ F := by
  constructor
  · intro div
    apply (modByMonic_eq_zero_iff_dvd mon).mp
    by_contra nonzero
    have rem : pencil A B u ∣ (F %ₘ M).map (algebraMap ℚ ℝ) := by
      rw [modByMonic_eq_sub_mul_div,Polynomial.map_sub,Polynomial.map_mul]
      exact dvd_sub div (hit.trans (dvd_mul_right _ _))
    have ne : M ≠ 1 := by rintro rfl; simp at nonzero
    exact (natDegree_modByMonic_lt F mon ne).not_ge
      (bound.trans (multiple_degree am small cop int nonzero rem))
  · intro h; exact hit.trans (Polynomial.map_dvd (algebraMap ℚ ℝ) h)

/-- The homogenized polynomial evaluated at `(A,-B)`. For a monic minimal
polynomial of degree `r`, this is the product of the conjugate pencils. -/
noncomputable def normForm {R : Type*} [CommRing R] (m A B : R[X]) : R[X] :=
  ∑ i ∈ range (m.natDegree+1),C (m.coeff i)*A^i*(-B)^(m.natDegree-i)

theorem normForm_top {m A B : ℚ[X]} (mm : m.Monic) (am : A.Monic)
    (pos : 0 < m.natDegree) (small : B.natDegree < A.natDegree) :
    (normForm m A B).Monic ∧ (normForm m A B).natDegree = m.natDegree*A.natDegree := by
  let r := m.natDegree
  let term (i : ℕ) := C (m.coeff i)*A^i*(-B)^(r-i)
  have positive : 0 < r*A.natDegree := Nat.mul_pos pos (by omega)
  have short (i : ℕ) (hi : i ∈ range r) : (term i).natDegree ≤ r*A.natDegree-1 := by
    have lt : i < r := mem_range.mp hi
    have strict := Nat.mul_lt_mul_of_pos_left small (show 0 < r-i by omega)
    have add : i*A.natDegree+(r-i)*A.natDegree = r*A.natDegree := by
      rw [←Nat.add_mul,show i+(r-i) = r by omega]
    have bound := natDegree_mul_le (p := C (m.coeff i)*A^i) (q := (-B)^(r-i))
    have first := natDegree_C_mul_le (m.coeff i) (A^i)
    simp only [natDegree_pow,natDegree_neg] at bound first
    dsimp only [term]
    omega
  have trim := natDegree_sum_le_of_forall_le (range r) term short
  have lt : (∑ i ∈ range r,term i).natDegree<(A^r).natDegree := by rw [natDegree_pow]; omega
  have eq : normForm m A B = (∑ i ∈ range r,term i)+A^r := by
    rw [normForm,sum_range_succ]
    simp only [term,r,mm.coeff_natDegree,C_1,one_mul,Nat.sub_self,pow_zero,mul_one]
  rw [eq]
  exact ⟨(am.pow r).add_of_right (degree_lt_degree lt),
    (natDegree_add_eq_right_of_natDegree_lt lt).trans (natDegree_pow A r)⟩

/-- A pencil divides the norm form of any rational polynomial annihilating
its parameter, without coprimality or degree hypotheses on the two masks. -/
theorem pencil_dvd_normForm (A B m : ℚ[X]) (u : ℝ) (ann : aeval u m = 0) :
    pencil A B u ∣ (normForm m A B).map (algebraMap ℚ ℝ) := by
  let T := A.map (algebraMap ℚ ℝ)
  let V := -(B.map (algebraMap ℚ ℝ))
  let r := m.natDegree
  let c (i : ℕ) : ℝ[X] := C ((algebraMap ℚ ℝ) (m.coeff i))
  have split : pencil A B u = T-C u*V := by simp [pencil,T,V]
  have sumzero : (∑ i ∈ range (r+1),c i*(C u*V)^i*V^(r-i)) = 0 := by
    have z : C (aeval u m)*V^r = 0 := by simp [ann]
    rw [←z,aeval_eq_sum_range,map_sum,sum_mul]
    apply sum_congr rfl
    intro i hi
    have e : i+(r-i) = r := by have := mem_range.mp hi; omega
    rw [mul_pow,Algebra.smul_def,map_mul,map_pow,show V^r = V^i*V^(r-i) by rw [←pow_add,e]]
    dsimp only [c]
    ring
  rw [split,normForm,Polynomial.map_sum]
  change T-C u*V ∣ ∑ i ∈ range (r+1),(C (m.coeff i)*A^i*(-B)^(r-i)).map _
  conv_rhs => rw [←sub_zero (∑ i ∈ _,_),←sumzero,←sum_sub_distrib]
  apply dvd_sum
  intro i _
  simp only [Polynomial.map_mul,map_C,Polynomial.map_pow,Polynomial.map_neg]
  change T-C u*V ∣ c i*T^i*V^(r-i)-c i*(C u*V)^i*V^(r-i)
  have h := sub_dvd_pow_sub_pow T (C u*V) i
  convert (h.mul_left (c i)).mul_right (V^(r-i)) using 1; ring

/-- The specialized algebraic pencil divides a rational mask exactly when
its explicit rational norm polynomial divides that mask. -/
theorem pencil_dvd_iff_norm {A B F : ℚ[X]} (am : A.Monic) (small : B.natDegree < A.natDegree)
    (cop : IsCoprime A B) {u : ℝ} (int : IsIntegral ℚ u) :
    pencil A B u ∣ F.map (algebraMap ℚ ℝ) ↔ normForm (minpoly ℚ u) A B ∣ F := by
  obtain ⟨mon,deg⟩ := normForm_top (minpoly.monic int) am (minpoly.natDegree_pos int) small
  exact least_multiple am small cop int mon deg.le (pencil_dvd_normForm _ _ _ _ (minpoly.aeval ℚ u))

private theorem map_normForm (m A B : ℤ[X]) :
    (normForm m A B).map (Int.castRingHom ℚ) = normForm (m.map (Int.castRingHom ℚ))
      (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) := by
  simp only [normForm,natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective),Polynomial.map_sum,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_neg,map_C,coeff_map]

/-- An integral pencil with monic leading mask gives divisibility in the
integer polynomial ring, so its norm also divides every integer evaluation. -/
theorem integral_norm_iff {A B F : ℤ[X]} (am : A.Monic) (small : B.natDegree < A.natDegree)
    (cop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    {u : ℝ} (int : IsIntegral ℤ u) :
    A.map (Int.castRingHom ℝ)+C u*B.map (Int.castRingHom ℝ) ∣ F.map (Int.castRingHom ℝ) ↔
      normForm (minpoly ℤ u) A B ∣ F := by
  let ι := Int.castRingHom ℚ
  have sm : (B.map ι).natDegree<(A.map ι).natDegree := by
    simpa only [natDegree_map_eq_of_injective (show Function.Injective ι from Int.cast_injective)] using small
  have field := pencil_dvd_iff_norm (F := F.map ι) (am.map ι) sm cop int.tower_top
  have mp : (minpoly ℤ u).map ι = minpoly ℚ u := (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ int).symm
  have mon : (normForm (minpoly ℤ u) A B).Monic := by
    apply monic_of_injective (f := ι) Int.cast_injective
    rw [show ι = Int.castRingHom ℚ from rfl,map_normForm,mp]
    exact (normForm_top (minpoly.monic int.tower_top) (am.map ι) (minpoly.natDegree_pos int.tower_top) sm).1
  rw [←map_dvd_map ι Int.cast_injective mon,show ι = Int.castRingHom ℚ from rfl,map_normForm,mp]
  simpa only [pencil,Polynomial.map_map,show (algebraMap ℚ ℝ).comp ι = Int.castRingHom ℝ from Subsingleton.elim _ _] using field

open Green28 Green28UniformSums Green28PrimitiveSupport
open scoped ENNReal

private theorem chart_least {P : PMF ℤ} {f : ℝ[X]} {l : ℤ} {s : ℝ} (m : Models P f l s)
    (fc : f.coeff 0 = 1) : IsLeast P.support l := by
  have pos : (P l).toReal = s := by simpa only [Nat.cast_zero,add_zero,fc,mul_one] using m.coeff 0
  refine ⟨(P.mem_support_iff _).mpr (fun off => ?_),fun z hz => ?_⟩
  · rw [off,ENNReal.toReal_zero] at pos; exact m.pos.ne pos
  · by_contra! below; exact (P.mem_support_iff _).mp hz (m.below _ below)

private theorem chart_unique {P : PMF ℤ} {f g : ℝ[X]} {a b : ℤ} {s t : ℝ}
    (m : Models P f a s) (n : Models P g b t) (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) : f = g := by
  obtain rfl := (chart_least m fc).unique (chart_least n gc)
  have eq := (m.coeff 0).symm.trans (n.coeff 0)
  simp only [fc,gc,mul_one] at eq
  subst t
  ext i
  exact mul_left_cancel₀ m.pos.ne' ((m.coeff i).symm.trans (n.coeff i))

/-- Any occupied output mask of the original independent integer laws must
contain the integral norm of a coprime marginal pencil. The opposite law has
no mass, width, or support cardinality restriction. -/
theorem norm_dvd_output {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) {A B : ℤ[X]} (am : A.Monic)
    (small : B.natDegree < A.natDegree)
    (cop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    {u : ℝ} (int : IsIntegral ℤ u) {b : ℤ} {t : ℝ}
    (model : Models Q (A.map (Int.castRingHom ℝ)+C u*B.map (Int.castRingHom ℝ)) b t)
    (ac : A.coeff 0 = 1) (bc : B.coeff 0 = 0) :
    normForm (minpoly ℤ u) A B ∣ outputMask S ne := by
  obtain ⟨f,g,a,c,s,v,_,n,_,_,_,_,_,gc,prod⟩ := mask_factorization ne sum
  have zero : (A.map (Int.castRingHom ℝ)+C u*B.map (Int.castRingHom ℝ)).coeff 0 = 1 := by
    simp [coeff_add,coeff_map,ac,bc]
  have same := chart_unique model n zero gc
  apply (integral_norm_iff am small cop int).mp
  exact ⟨f,by rw [same,←prod,mul_comm]⟩

/-- Evaluating the translated output mask at one counts the actual sum sites. -/
theorem outputMask_at_one (S : Finset ℤ) (ne : S.Nonempty) :
    (outputMask S ne).eval 1 = (S.card:ℤ) := by
  classical
  let shift (z : ℤ) := (z-S.min' ne).toNat
  have inj : Set.InjOn shift (S:Set ℤ) := by
    intro a ha b hb eq
    have l := S.min'_le _ ha; have r := S.min'_le _ hb
    dsimp [shift] at eq
    omega
  have sz : (S.image shift).card = S.card := card_image_of_injOn inj
  simp only [outputMask,eval_finsetSum,eval_monomial,one_pow,mul_one,sum_const,nsmul_eq_mul]
  exact_mod_cast sz

/-- Every evaluation of the norm divides the same evaluation of the
output mask. At one this gives divisibility of the number of sum outcomes. -/
theorem evaluated_norm_dvd_card {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) {A B : ℤ[X]} (am : A.Monic)
    (small : B.natDegree < A.natDegree)
    (cop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    {u : ℝ} (int : IsIntegral ℤ u) {b : ℤ} {t : ℝ}
    (model : Models Q (A.map (Int.castRingHom ℝ)+C u*B.map (Int.castRingHom ℝ)) b t)
    (ac : A.coeff 0 = 1) (bc : B.coeff 0 = 0) :
    (normForm (minpoly ℤ u) A B).eval 1 ∣ (S.card:ℤ) := by
  rw [←outputMask_at_one S ne]
  exact eval_dvd (x := (1:ℤ)) (norm_dvd_output ne sum am small cop int model ac bc)

#print axioms multiple_degree
#print axioms least_multiple
#print axioms normForm_top
#print axioms pencil_dvd_normForm
#print axioms pencil_dvd_iff_norm
#print axioms integral_norm_iff
#print axioms norm_dvd_output
#print axioms outputMask_at_one
#print axioms evaluated_norm_dvd_card
end Green28PencilNorm
