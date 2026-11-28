import Mathlib
/-! Integer factors in congruences of squares modulo powers of one prime. -/

namespace Arxiv.«2211.10788».LocalPower
private lemma nat_half {p a b h : ℕ} (hp : p.Prime) (dv : p^(2*h)∣a*b) :
    p^h∣a ∨ p^h∣b := by
  by_cases za : a=0
  · simp [za]
  by_cases zb : b=0
  · simp [zb]
  rw [hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero za zb),Nat.factorization_mul za zb,
    Finsupp.add_apply] at dv
  rw [hp.pow_dvd_iff_le_factorization za,hp.pow_dvd_iff_le_factorization zb]
  omega

theorem half_factors {p h : ℕ} (hp : p.Prime) {a b : ℤ} (dv : (p:ℤ)^(2*h)∣a*b) :
    (p:ℤ)^h∣a ∨ (p:ℤ)^h∣b := by
  have hab := Int.natAbs_dvd_natAbs.mpr dv
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at hab
  rcases nat_half hp hab with h|h
  · exact Or.inl (Int.natAbs_dvd_natAbs.mp (by simpa using h))
  · exact Or.inr (Int.natAbs_dvd_natAbs.mp (by simpa using h))

theorem square_split {p h : ℕ} (hp : p.Prime) {x z : ℤ}
    (eq : x^2 ≡ z^2 [ZMOD (p:ℤ)^(2*h)]) :
    x ≡ z [ZMOD (p:ℤ)^h] ∨ x ≡ -z [ZMOD (p:ℤ)^h] := by
  have dv := Int.modEq_iff_dvd.mp eq
  have factor : (p:ℤ)^(2*h)∣(z-x)*(z+x) := by
    convert dv using 1
    ring
  rcases half_factors hp factor with same|opposite
  · exact Or.inl (Int.modEq_iff_dvd.mpr same)
  · apply Or.inr
    apply Int.modEq_iff_dvd.mpr
    rwa [show -z-x = -(z+x) by ring,dvd_neg]

theorem cancel_twenty_two {p h f : ℕ} (hp : p.Prime) (dv : p^(h+1)∣22*f) : p^h∣f := by
  by_cases hf : f=0
  · simp [hf]
  have one : (22:ℕ).factorization p≤1 := by
    have sq : Squarefree (22:ℕ) := (Nat.squarefree_mul_iff (m:=2) (n:=11)).mpr
      ⟨by decide,Nat.prime_two.prime.squarefree,(by decide : Nat.Prime 11).prime.squarefree⟩
    exact ((Nat.squarefree_iff_factorization_le_one (by decide : (22:ℕ)≠0)).mp sq) p
  rw [hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero (by decide) hf),
    Nat.factorization_mul (by decide) hf,Finsupp.add_apply] at dv
  exact (hp.pow_dvd_iff_le_factorization hf).mpr (by omega)

#print axioms square_split

end Arxiv.«2211.10788».LocalPower
