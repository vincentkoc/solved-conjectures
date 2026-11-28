import CunninghamJonesSplitParity
import research.arxiv.«1104.1579».CunninghamJonesComplementaryOrders

/-! Irreducibility from complementary constant-term congruences. -/

namespace CunninghamChain.JonesSplitParity
open Polynomial

/-- An obstruction to assigning u and v as constant terms of complementary factors. -/
def SplitObstruction (m u v : ℕ) : Prop :=
  ∃ k p : ℕ, 2^(k+1) ∣ m-1 ∧ 2 < p ∧ p ∣ v ∧ Odd u ∧
    (u:ZMod (2^(k+1))) ≠ 1 ∧ (u:ZMod p)^2 = -1

private theorem no_factorization {m j u v : ℕ} {A B : ℤ[X]} (hm : 3 ≤ m) (hj : 0 < j)
    (hA : A.Monic) (hdeg : 0 < A.natDegree) (hAB : A*B=jonesSumPolynomial m j)
    (ha : A.coeff 0=(u:ℤ)) (hb : B.coeff 0=(v:ℤ)) (hv : 1<v)
    (obs : SplitObstruction m u v) : False := by
  obtain ⟨k,p,hk,hp,hpv,hu,hne,hs⟩ := obs
  apply incompatible_parities hk hp hpv hu hne hs (j:=j)
  · have h := (jones_factor_constant_congruence hm hj hA hdeg (hAB ▸ dvd_mul_right ..)).2
    simpa [ha] using h
  · have h := congrArg (fun x : ZMod v => x^2) (jones_factor_complementary_modulus hj hv hA hAB hb)
    simp only [mul_pow, ← pow_mul, ha, Int.cast_natCast, one_pow] at h
    rw [Nat.mul_comm (A.natDegree*j) 2,pow_mul,neg_one_sq,one_pow,one_mul] at h
    simpa only [← pow_mul,Nat.mul_comm 2 j] using h

/-- When every nontrivial splitting of m has an obstruction in at least one
orientation, every positive-degree geometric sum with constant m is irreducible. -/
theorem irreducible_all_degrees_of_splits {m : ℕ} (hm : 3 ≤ m)
    (cert : ∀ u v : ℕ, 1<u → 1<v → u*v=m →
      SplitObstruction m u v ∨ SplitObstruction m v u)
    {j : ℕ} (hj : 0<j) : Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape m j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at hdeg; omega,?_⟩
  intro A B hA hB hAB
  by_contra! hd
  have pos (D : ℤ[X]) (hD : D.Monic) (hn : D.natDegree ≠ 0) (hdiv : D ∣ jonesSumPolynomial m j) :
      1 < D.coeff 0 := by
    have := jones_factor_constant_gt_one (by omega) hD hdiv (Nat.pos_of_ne_zero hn)
    have := (jones_factor_constant_congruence hm hj hD (Nat.pos_of_ne_zero hn) hdiv).1
    omega
  have ha := pos A hA hd.1 (hAB ▸ dvd_mul_right ..)
  have hb := pos B hB hd.2 (hAB ▸ dvd_mul_left ..)
  let u := (A.coeff 0).toNat
  let v := (B.coeff 0).toNat
  have au : A.coeff 0=(u:ℤ) := by dsimp [u]; omega
  have bv : B.coeff 0=(v:ℤ) := by dsimp [v]; omega
  have hab : A.coeff 0 * B.coeff 0 = m := by
    simpa [jonesSumPolynomial,mul_coeff_zero,finsetSum_coeff,coeff_X_pow] using
      congrArg (fun P : ℤ[X] => P.coeff 0) hAB
  rw [au,bv] at hab
  rcases cert u v (by omega) (by omega) (by exact_mod_cast hab) with h|h
  · exact no_factorization hm hj hA (by omega) hAB au bv (by omega) h
  · exact no_factorization hm hj hB (by omega) (mul_comm A B ▸ hAB) bv au (by omega) h

#print axioms irreducible_all_degrees_of_splits

end CunninghamChain.JonesSplitParity
