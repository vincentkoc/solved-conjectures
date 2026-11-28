import CunninghamBalancedGapQuadratic
import CunninghamBalancedReciprocalExclusion
import CunninghamGapFactorReversal

/-! Eventual irreducibility of the balanced rational polynomial Cunningham chains. -/

namespace CunninghamChain.LinearRoots
open Polynomial LargeGap

private lemma unit_of_signed_reversal {a : ℕ} (ha : 2≤a) (k : Bool) {n : ℕ} (hn : 0<n)
    {A : ℤ[X]} (hc : IsUnit (A.coeff 0))
    (dvd : A ∣ polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n)
    {s : ℤ} (hs : s≠0) (rev : A.reverse=C s*A) : IsUnit A := by
  by_cases d : A.natDegree=0
  · rw [eq_C_of_natDegree_eq_zero d]
    exact isUnit_C.mpr hc
  have ne : A≠0 := by rintro rfl; simp at d
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ A (by
    rw [degree_eq_natDegree ne]; exact_mod_cast d)
  have z0 : z≠0 := by
    rintro rfl
    have hz' : (A.coeff 0 : ℂ)=0 := by simpa [aeval_def,←eval_map,←coeff_zero_eq_eval_zero] using hz
    exact hc.ne_zero (Int.cast_eq_zero.mp hz')
  let : Invertible z := invertibleOfNonzero z0
  have ir : aeval z⁻¹ A.reverse=0 := by
    simpa only [aeval_def,invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (algebraMap ℤ ℂ) z A).mpr hz
  rw [rev,map_mul,aeval_C] at ir
  have hi : aeval z⁻¹ A=0 := (mul_eq_zero.mp ir).resolve_left (by change (s:ℂ)≠0; exact_mod_cast hs)
  have root (x : ℂ) (hr : aeval x A=0) : aeval x (term k a (-a) n)=0 := by
    have comp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)=algebraMap ℤ ℂ := Subsingleton.elim _ _
    have h := aeval_dvd (x:=x) dvd
    rw [hr,zero_dvd_iff] at h
    simpa only [term,aeval_def,eval₂_map,comp] using h
  exact (balanced_no_reciprocal_roots (a:=(a:ℤ)) (by omega) k hn z0 (root _ hz) (root _ hi)).elim

/-- From the explicit gap threshold onward, the first-kind rational iterate is
irreducible for every a≥2. For the second kind a nonsquare coefficient suffices. -/
theorem eventual_balanced_iterate_of_gap {a : ℕ} (ha : 2≤a) (k : Bool)
    (ok : k=true ∨ ¬IsSquare a) {n : ℕ} (hn : 0<n)
    (large : gapThreshold (gapEndpoint a k)≤n+2) : Irreducible (term k a (-a) n) := by
  let seed : ℤ[X] := C (a:ℤ)*X+C (-(a:ℤ))
  let T := polynomialTerm k seed n
  let L : ℤ[X] := C (-sign k)*(X-1)
  have a0 : (a:ℤ)≠0 := by omega
  have ds : seed.natDegree=1 := natDegree_linear a0
  have dt : T.natDegree=1+n := (polynomialTerm_shape k seed (by omega) n).1.trans (by rw [ds])
  have tn : T≠0 := by intro h; simp [h] at dt; omega
  have ct : IsUnit (T.coeff 0) := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    dsimp [T]
    rw [hi]
    cases k <;> simp [polynomialTerm]
  have primitive : T.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun c hc =>
    isUnit_of_dvd_unit ((C_dvd_iff_dvd_coeff ..).mp hc 0) ct
  change Irreducible (T.map (Int.castRingHom ℚ))
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast primitive).mp
  refine ⟨fun h => by have := natDegree_eq_zero_of_isUnit h; omega,?_⟩
  intro A B hab
  have nz : A≠0 ∧ B≠0 := mul_ne_zero_iff.mp (hab ▸ tn)
  have dl : L.natDegree≤1 := by
    dsimp only [L]
    compute_degree
  have rl : reflect 1 L= -L := by
    rw [show L=C (-sign k)*(X-1) by rfl,reflect_C_mul,reflect_sub]
    simp
    ring
  have ln : L≠0 := mul_ne_zero (by cases k <;> simp [sign]) (by simpa using X_sub_C_ne_zero (1:ℤ))
  have size : n+2=1+(A.natDegree+B.natDegree) := by
    rw [hab,natDegree_mul nz.1 nz.2] at dt
    omega
  have eq : separated (gapEndpoint a k) (n+2)=L*(A*B) := by
    rw [separated_gap_endpoint,←hab]
    dsimp only [L,T,seed]
    ring
  obtain ⟨s,hs,h|h⟩ := factor_reversal L A B _ (gap_endpoint_irreducible ha k ok)
    large ln nz.1 nz.2 dl rl size eq
  · refine Or.inl (unit_of_signed_reversal ha k hn ?_ ⟨B,hab⟩ ?_ h)
    · rw [hab,mul_coeff_zero] at ct
      exact isUnit_of_mul_isUnit_left ct
    · intro no; simp [no] at hs
  · refine Or.inr (unit_of_signed_reversal ha k hn ?_ ⟨A,hab.trans (mul_comm ..)⟩ ?_ h)
    · rw [hab,mul_coeff_zero] at ct
      exact isUnit_of_mul_isUnit_right ct
    · intro no; simp at no; simp [no] at hs

/-- A single finite prefix decides whether a nonsquare coefficient works at
every index in both rational polynomial chains from the same seed. -/
theorem simultaneous_balanced_iff_finite {a : ℕ} (ha : 2≤a) (nonSquare : ¬IsSquare a) :
    (∀ (k : Bool) (n : ℕ), Irreducible (term k a (-a) n)) ↔
    ∀ (k : Bool) (n : ℕ), n < max 1 (max (gapThreshold (gapEndpoint a true))
      (gapThreshold (gapEndpoint a false))) → Irreducible (term k a (-a) n) := by
  constructor
  · exact fun h k n _ => h k n
  intro h k n
  by_cases small : n < max 1 (max (gapThreshold (gapEndpoint a true)) (gapThreshold (gapEndpoint a false)))
  · exact h k n small
  apply eventual_balanced_iterate_of_gap ha k (Or.inr nonSquare) (by omega)
  cases k <;> omega

/-- The second-kind cubic-index exception at a=2 shows why a finite prefix matters. -/
theorem reducible_second_at_two_three : ¬Irreducible (term false 2 (-2) 3) := by
  have eq : term false 2 (-2) 3=(X^2-X-1)*((2:ℚ[X])*X^2+1) := by
    norm_num [term,polynomialTerm]
    ring
  intro h
  rcases h.isUnit_or_isUnit eq with u|u
  · have d := natDegree_eq_zero_of_isUnit u
    have d' : (X^2-X-1:ℚ[X]).natDegree=2 := by compute_degree!
    omega
  · have d := natDegree_eq_zero_of_isUnit u
    have d' : ((2:ℚ[X])*X^2+1).natDegree=2 := by compute_degree!
    omega

#print axioms eventual_balanced_iterate_of_gap
#print axioms simultaneous_balanced_iff_finite
#print axioms reducible_second_at_two_three

end CunninghamChain.LinearRoots
