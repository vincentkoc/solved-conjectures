import CunninghamJonesMultiplicityProduct
import CunninghamJonesLinearFactors

/-! Coefficients of a Jones sum after translating X by one, modulo 3 and 9. -/

namespace CunninghamChain.JonesMultiplicity
open Polynomial
open scoped Polynomial

private lemma binomial_first {R : Type*} [CommRing R] (x : R) (d : ℕ) :
    ∃ w : R, (1+x)^d=1+(d:R)*x+x^2*w := by
  induction d with
  | zero => exact ⟨0,by simp⟩
  | succ d ih =>
    obtain ⟨w,hw⟩ := ih
    exact ⟨d+w+x*w,by rw [pow_succ,hw,Nat.cast_succ]; ring⟩

private lemma cube_lift (A B : ℤ[X])
    (h : A.map (Int.castRingHom (ZMod 3))=B.map (Int.castRingHom (ZMod 3))) :
    (A^3).map (Int.castRingHom (ZMod 9))=(B^3).map (Int.castRingHom (ZMod 9)) := by
  have dvd : C (3:ℤ) ∣ A-B := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    have hh := congrArg (fun P : (ZMod 3)[X] => P.coeff i) h
    simpa [coeff_map,coeff_sub] using sub_eq_zero.mpr hh
  obtain ⟨H,hH⟩ := dvd
  have eq : A=B+C 3*H := by linear_combination hH
  have hc : A^3-B^3=C 9*(H*B^2+3*B*H^2+3*H^3) := by
    rw [eq,show C (3:ℤ)=(3:ℤ[X]) from map_ofNat C 3,
      show C (9:ℤ)=(9:ℤ[X]) from map_ofNat C 9]; ring
  apply sub_eq_zero.mp
  rw [←Polynomial.map_sub,hc,Polynomial.map_mul,map_C]
  rw [show (Int.castRingHom (ZMod 9)) (9:ℤ)=0 by decide,C_0,zero_mul]

private lemma cube_profile (n : ℕ) :
    (1+X : (ZMod 9)[X])^(3^(n+1))=(1+X^(3^n))^3 := by
  have h : ((1+X : ℤ[X])^(3^n)).map (Int.castRingHom (ZMod 3)) =
      (1+X^(3^n) : ℤ[X]).map (Int.castRingHom (ZMod 3)) := by
    simp only [Polynomial.map_pow,Polynomial.map_add,Polynomial.map_one,Polynomial.map_X]
    rw [add_pow_char_pow]; simp
  have c := cube_lift _ _ h
  simpa only [Polynomial.map_pow,Polynomial.map_add,Polynomial.map_one,Polynomial.map_X,
    pow_succ (3:ℕ) n,pow_mul] using c

private lemma translated_identity (m j c : ℕ) (hm : c ∣ m) :
    X*((jonesSumPolynomial m j).comp (X+1)).map (Int.castRingHom (ZMod c)) =
      (1+X)*((1+X)^j-1) := by
  let φ := Int.castRingHom (ZMod c)
  have h0 : φ (m:ℤ)=0 := by simpa [φ] using (ZMod.natCast_eq_zero_iff ..).mpr hm
  have red : (jonesSumPolynomial m j).map φ =
      X*∑ i∈Finset.range j,(X : (ZMod c)[X])^i := by
    simp only [jonesSumPolynomial,Polynomial.map_add,map_C,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_X,h0,C_0,zero_add,Finset.mul_sum,pow_succ']
  have geom := geom_sum_mul (1+X : (ZMod c)[X]) j
  simp only [add_sub_cancel_left] at geom
  rw [map_comp,red,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,mul_comp,X_comp,
    sum_comp]
  simp only [pow_comp,X_comp]
  rw [add_comm (X : (ZMod c)[X]) 1,←geom]
  ring

private lemma first_from_power {m c j d h : ℕ} (hh : 0<h) (hm : c ∣ m)
    (hc : (d:ZMod c)≠0) (he : (1+X : (ZMod c)[X])^j=(1+X^h)^d) :
    FirstCoefficientMod c ((jonesSumPolynomial m j).comp (X+1)) (h-1) := by
  let A := ((jonesSumPolynomial m j).comp (X+1)).map (Int.castRingHom (ZMod c))
  obtain ⟨w,hw⟩ := binomial_first (X^h : (ZMod c)[X]) d
  let V : (ZMod c)[X] := (1+X)*(C (d:ZMod c)+X^h*w)
  have v0 : V.coeff 0≠0 := by simpa [V,mul_coeff_zero,coeff_X_pow,hh.ne',hh.ne] using hc
  have rel := translated_identity m j c hm
  change X*A=_ at rel
  rw [he,hw] at rel
  have shape : A=X^(h-1)*V := by
    apply isRegular_X.left
    change X*A=X*(X^(h-1)*V)
    rw [rel,←mul_assoc,←pow_succ',Nat.sub_add_cancel hh]
    dsimp [V]
    simp only [map_natCast]
    ring
  have coeff (i : ℕ) : (Int.castRingHom (ZMod c)) (((jonesSumPolynomial m j).comp (X+1)).coeff i)
      = if h-1 ≤ i then V.coeff (i-(h-1)) else 0 := by
    simpa only [A,coeff_map,coeff_X_pow_mul'] using congrArg (fun P : (ZMod c)[X] => P.coeff i) shape
  constructor
  · intro i hi
    have e := coeff i
    rw [if_neg hi.not_ge] at e
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mp e
  · intro hi
    have H := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hi
    have e := coeff (h-1)
    rw [if_pos le_rfl,Nat.sub_self] at e
    exact v0 (e.symm.trans H)

/-- At degree 3^(n+1)d with 3∤d and 9∣m, the translated Jones sum first
survives modulo 3 at 3^(n+1)−1 and modulo 9 at 3^n−1. -/
theorem jones_translated_first_coefficients {m d : ℕ} (hm : 9 ∣ m) (hd : ¬3 ∣ d) (n : ℕ) :
    let T := (jonesSumPolynomial m (3^(n+1)*d)).comp (X+1)
    FirstCoefficientMod 3 T (3^(n+1)-1) ∧ FirstCoefficientMod 9 T (3^n-1) := by
  dsimp only
  constructor
  · apply first_from_power (d:=d) (by positivity) ((by decide : 3∣9).trans hm)
      ((ZMod.natCast_eq_zero_iff ..).not.mpr hd)
    rw [pow_mul,add_pow_char_pow]; simp
  · have h9 : ¬9 ∣ 3*d := by
      intro h
      exact hd ((Nat.mul_dvd_mul_iff_left (by decide : 0<3)).mp h)
    apply first_from_power (m:=m) (c:=9) (j:=3^(n+1)*d) (h:=3^n) (d:=3*d) (by positivity) hm ((ZMod.natCast_eq_zero_iff ..).not.mpr h9)
    rw [pow_mul,cube_profile,pow_mul]

#print axioms jones_translated_first_coefficients

end CunninghamChain.JonesMultiplicity
