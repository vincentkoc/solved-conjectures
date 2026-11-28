import Mathlib

/-! The first coefficient surviving modulo a prime square in a product. -/

namespace CunninghamChain.JonesMultiplicity
open Polynomial
open scoped Polynomial

/-- The coefficient of degree e is the first one not divisible by m. -/
def FirstCoefficientMod (m : ℤ) (A : ℤ[X]) (e : ℕ) : Prop :=
  (∀ i < e, m ∣ A.coeff i) ∧ ¬m ∣ A.coeff e

private lemma below_min {p : ℤ} {A B : ℤ[X]} {e f k : ℕ}
    (ha : FirstCoefficientMod p A e) (hb : FirstCoefficientMod p B f)
    (hke : k<e) (hkf : k<f) : p^2 ∣ (A*B).coeff k := by
  rw [pow_two,coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  exact mul_dvd_mul (ha.1 ij.1 (by omega)) (hb.1 ij.2 (by omega))

private lemma at_shorter {p : ℤ} (hp : Prime p) {A B : ℤ[X]} {e f : ℕ}
    (ha : FirstCoefficientMod p A e) (hb : FirstCoefficientMod p B f)
    (he : 0<e) (hef : e<f) (h0 : ¬p^3 ∣ (A*B).coeff 0) :
    ¬p^2 ∣ (A*B).coeff e := by
  intro h
  let I := Finset.HasAntidiagonal.antidiagonal e
  have mem : (e,0)∈I := Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero _)
  have rest : p^2 ∣ ∑ ij ∈ I.erase (e,0), A.coeff ij.1*B.coeff ij.2 := by
    apply Finset.dvd_sum
    intro ij hij
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hij
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem
    have hi : ij.1<e := by
      by_contra! bad
      exact hne (Prod.ext (by omega) (by omega))
    rw [pow_two]
    exact mul_dvd_mul (ha.1 _ hi) (hb.1 _ (by omega))
  rw [coeff_mul] at h
  change p^2 ∣ ∑ ij ∈ I, A.coeff ij.1*B.coeff ij.2 at h
  rw [←Finset.sum_erase_add _ _ mem] at h
  have last := (dvd_add_right rest).mp h
  change p^2 ∣ A.coeff e * B.coeff 0 at last
  obtain ⟨z,hz⟩ := hb.1 0 (by omega)
  have can : p*p ∣ p*(A.coeff e*z) := by simpa only [pow_two,hz,mul_left_comm] using last
  have div := (mul_dvd_mul_iff_left hp.ne_zero).mp can
  have hz' := (hp.dvd_mul.mp div).resolve_left ha.2
  apply h0
  rw [mul_coeff_zero,hz,show p^3=p*(p*p) by ring]
  exact mul_dvd_mul (ha.1 0 he) (mul_dvd_mul_left p hz')

/-- If the first coefficient surviving modulo p² occurs before the
midpoint of the total multiplicity modulo p, it locates the shorter
positive multiplicity of the factors. -/
theorem shorter_multiplicity {p : ℤ} (hp : Prime p) {A B : ℤ[X]} {e f t : ℕ}
    (ha : FirstCoefficientMod p A e) (hb : FirstCoefficientMod p B f)
    (ht : FirstCoefficientMod (p^2) (A*B) t) (h0 : ¬p^3 ∣ (A*B).coeff 0)
    (he : 0<e) (hf : 0<f) (hmid : 2*t<e+f) : min e f=t := by
  have hle : min e f≤t := by
    by_contra! h
    exact ht.2 (below_min ha hb (lt_min_iff.mp h).1 (lt_min_iff.mp h).2)
  rcases lt_trichotomy e f with h|h|h
  · rw [min_eq_left h.le] at hle ⊢
    exact le_antisymm hle (by by_contra! hlt; exact at_shorter hp ha hb he h h0 (ht.1 _ hlt))
  · subst f
    simp only [min_self] at hle
    omega
  · rw [min_eq_right h.le] at hle ⊢
    have h0' : ¬p^3 ∣ (B*A).coeff 0 := by rwa [mul_comm]
    exact le_antisymm hle (by
      by_contra! hlt
      exact at_shorter hp hb ha hf h h0' (by simpa only [mul_comm B A] using ht.1 _ hlt))

#print axioms shorter_multiplicity

end CunninghamChain.JonesMultiplicity
