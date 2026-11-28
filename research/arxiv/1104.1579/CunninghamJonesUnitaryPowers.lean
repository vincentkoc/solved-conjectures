import CunninghamJonesSplitCriterion

/-! Coprime constant factors of Jones polynomials and stability under odd powers. -/

namespace CunninghamChain.JonesSplitParity

/-- A factorization with coprime, nonunit factors must admit a parity obstruction
in one orientation. Such factorizations are also called unitary splits. -/
def UnitarySplitCertificate (m : ℕ) : Prop :=
  ∀ u v : ℕ, 1 < u → 1 < v → u*v=m → u.Coprime v →
    SplitObstruction m u v ∨ SplitObstruction m v u

/-- An odd power preserves each parity obstruction, including its prime divisor
on the opposite side of the split. -/
theorem SplitObstruction.odd_pow {m u v h : ℕ} (obs : SplitObstruction m u v) (hh : Odd h) :
    SplitObstruction (m^h) (u^h) (v^h) := by
  have hnz : h ≠ 0 := by obtain ⟨s,hs⟩ := hh; omega
  obtain ⟨k,p,hm,hp,hv,hu,hn,hs⟩ := obs
  refine ⟨k,p,hm.trans (Nat.sub_one_dvd_pow_sub_one m h),hp,
    hv.trans (dvd_pow_self v hnz),hu.pow,?_,?_⟩
  · rw [Nat.cast_pow]
    exact fun he => (Nat.not_even_iff_odd.mpr hh) (even_exponent_mod_two_power hu hn he)
  · rw [Nat.cast_pow,←pow_mul,Nat.mul_comm h 2,pow_mul,hs,hh.neg_one_pow]

/-- Once a coefficient passes the unitary-split test, each of its odd powers
passes the same test. -/
theorem UnitarySplitCertificate.odd_pow {m h : ℕ} (cert : UnitarySplitCertificate m)
    (hh : Odd h) : UnitarySplitCertificate (m^h) := by
  have hnz : h ≠ 0 := by obtain ⟨s,hs⟩ := hh; omega
  intro u v hu hv he hc
  have unit {x y : ℕ} (hxy : x.Coprime y) : IsUnit (GCDMonoid.gcd x y) := by
    change IsUnit (x.gcd y)
    simp [hxy.gcd_eq_one]
  obtain ⟨a,rfl⟩ := exists_eq_pow_of_mul_eq_pow (unit hc) he
  obtain ⟨b,rfl⟩ := exists_eq_pow_of_mul_eq_pow (unit hc.symm) ((Nat.mul_comm ..).trans he)
  have hab : a*b=m := Nat.pow_left_injective hnz (by simpa only [mul_pow] using he)
  have hca : a.Coprime b := (hc.of_dvd_left (dvd_pow_self a hnz)).of_dvd_right
    (dvd_pow_self b hnz)
  have gt (x : ℕ) (hx : 1 < x^h) : 1 < x := by
    by_contra! hn
    exact (not_lt_of_ge (show x^h ≤ 1 by simpa using Nat.pow_le_pow_left hn h)) hx
  exact (cert a b (gt _ hu) (gt _ hv) hab hca).imp (fun z => z.odd_pow hh) (fun z => z.odd_pow hh)

#print axioms SplitObstruction.odd_pow
#print axioms UnitarySplitCertificate.odd_pow

end CunninghamChain.JonesSplitParity
