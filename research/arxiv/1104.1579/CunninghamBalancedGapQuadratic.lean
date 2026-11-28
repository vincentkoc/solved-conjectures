import CunninghamLargeGapRigidity
import CunninghamLinearReciprocalRoots

/-! The quadratic endpoint of the sparse polynomial attached to a balanced Jones iterate. -/

namespace CunninghamChain.LinearRoots
open Polynomial LargeGap

noncomputable def gapQuadratic (a : ℕ) (k : Bool) : ℤ[X] :=
  C (a:ℤ)-C (2*(a:ℤ))*X+C ((a:ℤ)+sign k)*X^2

/-- The sign normalizes the isolated coefficient in (X−1)Tₙ to one. -/
noncomputable def gapEndpoint (a : ℕ) (k : Bool) : ℤ[X] :=
  C (-sign k)*gapQuadratic a k

lemma quadratic_ends {a : ℕ} (ha : 2 ≤ a) (k : Bool) :
    (gapQuadratic a k).coeff 0=a ∧ (gapQuadratic a k).coeff 2=(a:ℤ)+sign k ∧
    (gapQuadratic a k).natDegree=2 := by
  have hn : (a:ℤ)+sign k≠0 := by cases k <;> simp [sign] <;> omega
  have low : (gapQuadratic a k).coeff 0=a := by simp [gapQuadratic]
  have hi : (gapQuadratic a k).coeff 2=(a:ℤ)+sign k := by
    simp only [gapQuadratic,coeff_add,coeff_sub,coeff_C_mul,coeff_X,coeff_X_pow,coeff_C]
    norm_num
  refine ⟨low,hi,le_antisymm ?_ (le_natDegree_of_ne_zero (hi ▸ hn))⟩
  unfold gapQuadratic
  compute_degree

/-- The sparse quadratic is irreducible at every a≥2 for the plus chain,
and for the minus chain whenever a is a nonsquare. -/
theorem gap_endpoint_irreducible {a : ℕ} (ha : 2 ≤ a) (k : Bool) (ok : k=true ∨ ¬IsSquare a) :
    Irreducible (gapEndpoint a k) := by
  let P := gapQuadratic a k
  obtain ⟨lo,hi,deg⟩ := quadratic_ends ha k
  have primitive : P.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun d hd => by
    have all := (C_dvd_iff_dvd_coeff ..).mp hd
    have d0 : d ∣ (a:ℤ) := lo ▸ all 0
    have d2 : d ∣ (a:ℤ)+sign k := hi ▸ all 2
    have unit : d ∣ sign k := by simpa using dvd_sub d2 d0
    exact isUnit_of_dvd_unit unit (by cases k <;> simp [sign])
  have overQ : Irreducible (P.map (Int.castRingHom ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_map_eq_of_injective Int.cast_injective,deg]
      decide
    intro x hx
    have eq : (a:ℚ)*(1-x)^2+(sign k:ℚ)*x^2=0 := by
      simp [P,gapQuadratic,IsRoot.def] at hx
      linear_combination hx
    have aPos : (0:ℚ) < a := by exact_mod_cast (by omega : 0 < a)
    cases k with
    | true =>
      simp [sign] at eq
      have zero : x^2=0 := by nlinarith [mul_nonneg aPos.le (sq_nonneg (1-x)),sq_nonneg x]
      have x0 : x=0 := by simpa using zero
      simp [x0] at eq
      omega
    | false =>
      simp [sign] at eq ok
      have xm : 1-x≠0 := by intro no; rw [show x=1 by linarith] at eq; norm_num at eq
      apply ok
      apply Rat.isSquare_natCast_iff.mp
      refine ⟨x/(1-x),?_⟩
      field_simp
      nlinarith
  have overZ := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast primitive).mpr overQ
  cases k
  · simpa [gapEndpoint,sign,P] using overZ
  · have hneg : Irreducible (-P) := Associated.irreducible ⟨-1, mul_neg_one P⟩ overZ
    simpa [gapEndpoint,sign,P] using hneg

private lemma reflect_gap (a : ℕ) (k : Bool) (n : ℕ) :
    reflect (n+2) (gapQuadratic a k)=X^n*(C (a:ℤ)*(X-1)^2+C (sign k)) := by
  have lin : reflect (n+2) (C (2*(a:ℤ))*X)=C (2*(a:ℤ))*X^(revAt (n+2) 1) := by
    simpa only [pow_one] using (reflect_C_mul_X_pow (n+2) 1 (c:=2*(a:ℤ)))
  unfold gapQuadratic
  rw [reflect_add,reflect_sub,reflect_C,lin,reflect_C_mul_X_pow]
  rw [revAt_le (by omega : 1 ≤ n+2),revAt_le (by omega : 2 ≤ n+2)]
  simp only [show n+2-1=n+1 by omega,show n+2-2=n by omega,pow_add,pow_one,map_add,map_mul]
  rw [show (C (2:ℤ):ℤ[X])=2 by norm_num]
  ring

/-- Exact identification between the separated polynomial and the normalized iterate. -/
theorem separated_gap_endpoint (a : ℕ) (k : Bool) (n : ℕ) :
    separated (gapEndpoint a k) (n+2) =
      C (-sign k)*((X-1)*polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n) := by
  have tel : (X-1)*polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n =
      X^n*(C (a:ℤ)*(X-1)^2+C (sign k))-C (sign k) := by
    induction n with
    | zero => simp [polynomialTerm]; ring
    | succ i ih =>
      change (X-1)*(X*polynomialTerm k _ i+C (sign k))=_
      calc _ = X*((X-1)*polynomialTerm k _ i)+(X-1)*C (sign k) := by ring
           _ = _ := by rw [ih,pow_succ]; ring
  rw [tel,separated,gapEndpoint,reflect_C_mul,reflect_gap]
  cases k <;> simp [sign] <;> ring

#print axioms gap_endpoint_irreducible
#print axioms separated_gap_endpoint

end CunninghamChain.LinearRoots
