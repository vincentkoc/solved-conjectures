import Mathlib

/-! Arithmetic restrictions from the integer equation for a signed rational-root denominator. -/

namespace CunninghamChain.LinearRoots
open Finset

private lemma coprime_adjacent (d : ℤ) : IsCoprime d (d-1) :=
  ⟨1,-1,by ring⟩

private lemma sub_square_dvd_iff (d : ℤ) (hd : d≠1) (n : ℕ) :
    (d-1)^2 ∣ d^n-1 ↔ d-1 ∣ (n:ℤ) := by
  rw [←geom_sum_mul,pow_two,mul_dvd_mul_iff_right (sub_ne_zero.mpr hd)]
  simpa using (dvd_geom_sum₂_iff_of_dvd_sub (n:=n) (x:=d) (y:=1) (p:=d-1) (dvd_refl _))

/-- The signed denominator differs from one by a divisor of the index. Its square
is a unitary divisor of the coefficient. -/
theorem root_denominator_arithmetic {a n : ℕ} {d e : ℤ} (hd : 2≤d.natAbs) (hn : 0<n)
    (he : e^2=1) (h : (a:ℤ)*(d-1)^2=e*d^2*(d^n-1)) :
    d-1 ∣ (n:ℤ) ∧ ∃ b : ℕ, a=d.natAbs^2*b ∧ d.natAbs.Coprime b := by
  have hd0 : d≠0 := by omega
  have hd1 : d≠1 := by omega
  have hc : IsCoprime (d^2) ((d-1)^2) := (coprime_adjacent d).pow
  have h' : d^2*(d^n-1)=e*a*(d-1)^2 := by linear_combination -e*h-(d^2*(d^n-1))*he
  have hminus : (d-1)^2∣d^n-1 :=
    hc.symm.dvd_of_dvd_mul_left (h' ▸ dvd_mul_left _ _)
  refine ⟨(sub_square_dvd_iff d hd1 n).mp hminus,?_⟩
  have ha : d^2∣(a:ℤ) := hc.dvd_of_dvd_mul_right (h ▸ (dvd_mul_of_dvd_left (dvd_mul_left ..) _))
  obtain ⟨t,ht⟩ := ha
  have et : t*(d-1)^2=e*(d^n-1) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd0)
    rw [ht] at h
    linear_combination h
  have cop : IsCoprime d t := by
    refine ⟨d^(n-1),-e*(d-1)^2,?_⟩
    rw [←pow_succ,show n-1+1=n by omega]
    linear_combination -e*et-(d^n-1)*he
  refine ⟨t.natAbs,?_,Int.isCoprime_iff_gcd_eq_one.mp cop⟩
  simpa only [Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs ht

/-- Every such divisor of a positive index actually supplies a positive coefficient and a sign. -/
theorem exists_scaled_root_equation {d : ℤ} {n : ℕ} (hd : 2≤d.natAbs) (hn : 0<n)
    (h : d-1 ∣ (n:ℤ)) : ∃ a : ℕ, 0<a ∧ ∃ e : ℤ, (e=1 ∨ e= -1) ∧
      (a:ℤ)*(d-1)^2=e*d^2*(d^n-1) := by
  have hd1 : d≠1 := by omega
  obtain ⟨t,ht⟩ := (sub_square_dvd_iff d hd1 n).mpr h
  have ht0 : t≠0 := by
    rintro rfl
    have e : d^n=1 := by omega
    have ea := congrArg Int.natAbs e
    simp only [Int.natAbs_pow,Int.natAbs_one] at ea
    exact (one_lt_pow₀ (by omega : 1<d.natAbs) hn.ne').ne' ea
  refine ⟨d.natAbs^2*t.natAbs,Nat.mul_pos (pow_pos (by omega) _) (Int.natAbs_pos.mpr ht0),?_⟩
  have ds : (d.natAbs:ℤ)^2=d^2 := Int.natAbs_sq d
  rcases Int.natAbs_eq t with he|he
  · refine ⟨1,Or.inl rfl,?_⟩
    simp only [Nat.cast_mul,Nat.cast_pow]; rw [ds,←he,ht]; ring
  · refine ⟨-1,Or.inr rfl,?_⟩
    have e : (t.natAbs:ℤ)= -t := by omega
    simp only [Nat.cast_mul,Nat.cast_pow]; rw [ds,e,ht]; ring

#print axioms root_denominator_arithmetic
#print axioms exists_scaled_root_equation

end CunninghamChain.LinearRoots
