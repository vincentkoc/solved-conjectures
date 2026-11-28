import CunninghamCollisionTrinomial

/-! Koley and Reddy's cyclotomic/noncyclotomic split for the collision trinomial. -/

namespace CunninghamChain.SharedFactors
open Polynomial

private lemma one_of_re {z : ℂ} (hz : ‖z‖ ≤ 1) (hr : 1 ≤ z.re) : z = 1 := by
  have he := le_antisymm ((Complex.re_le_norm _).trans hz) hr
  have h := Complex.sq_norm_sub_sq_re z
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im, mul_self_le_mul_self (norm_nonneg z) hz]
  exact Complex.ext (by simpa using he) (by simpa using him)

private lemma two_powers {w : ℂ} {i j : ℕ} (hw : ‖w‖ ≤ 1)
    (hc : Nat.Coprime i j) (h : w^i+w^(i+j)=2) : w=1 := by
  have hn (k : ℕ) : ‖w^k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  have hr := congrArg Complex.re h
  change (w^i).re+(w^(i+j)).re=2 at hr
  have hs (k : ℕ) := (Complex.re_le_norm (w^k)).trans (hn k)
  have hi : w^i=1 := one_of_re (hn i) (by linarith [hs (i+j)])
  have hij : w^(i+j)=1 := one_of_re (hn _) (by linarith [hs i])
  have hj : w^j=1 := by simpa [pow_add,hi] using hij
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hi) (orderOf_dvd_of_pow_eq_one hj)
  have ho := Nat.dvd_one.mp (hc ▸ hd : orderOf w ∣ 1)
  simpa [ho] using pow_orderOf_eq_one w

private lemma cofactor_inside {g i j : ℕ} (hi : 0 < i) (hc : Nat.Coprime i j) (z : ℂ)
    (hz : ((cofactor g i j).map (Int.castRingHom ℂ)).IsRoot z) : ‖z‖ < 1 := by
  by_contra! hnorm
  have h0 : z ≠ 0 := by rintro rfl; norm_num at hnorm
  let w := z^g
  have hw : w ≠ 0 := pow_ne_zero _ h0
  have hw1 : 1 ≤ ‖w‖ := by dsimp [w]; rw [norm_pow]; exact one_le_pow₀ hnorm
  have e := congrArg (fun P : ℤ[X] => (P.map (Int.castRingHom ℂ)).eval z)
    (cofactor_identity g i j)
  change ((cofactor g i j).map (Int.castRingHom ℂ)).eval z = 0 at hz
  have he : (2:ℂ)*w^(i+j)=w^j+1 := by
    simpa [Polynomial.map_sub,Polynomial.map_add,hz,pow_mul,w,sub_eq_zero] using e.symm
  have powEq : (w⁻¹)^i+(w⁻¹)^(i+j)=2 := by
    rw [inv_pow,inv_pow,pow_add]
    rw [pow_add] at he
    field_simp [hw]
    linear_combination -he
  have hw' : w⁻¹=1 := two_powers (by rwa [norm_inv,inv_le_one₀ (norm_pos_iff.mpr hw)]) hc powEq
  have hwEq : z^g=1 := by simpa [w] using congrArg Inv.inv hw'
  have nonzero : (i+j:ℂ)+i ≠ 0 := by exact_mod_cast (show i+j+i≠0 by omega)
  apply nonzero
  simpa [cofactor,geom,Polynomial.map_sum,eval_finsetSum,pow_mul,hwEq] using hz

/-- Removing the roots of unity from the trinomial leaves an irreducible rational polynomial. -/
theorem cofactor_irreducible {g i j : ℕ} (hg : 0 < g) (hi : 0 < i) (hj : 0 < j)
    (hc : Nat.Coprime i j) : Irreducible ((cofactor g i j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hd,hl⟩ := cofactor_shape (j := j) hg hi
  apply irreducible_of_prime_leading_inside
  · have := Nat.mul_le_mul_left g (show 2 ≤ i+j by omega)
    omega
  · rw [cofactor_zero hg hi hj]; exact isUnit_one
  · rw [hl]; exact Int.prime_iff_natAbs_prime.mpr (by decide) |>.irreducible
  · exact cofactor_inside hi hc

#print axioms cofactor_irreducible

end CunninghamChain.SharedFactors
