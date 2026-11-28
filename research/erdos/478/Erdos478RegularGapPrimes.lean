import Erdos478GapSplittingTest
import Erdos478DisjointGapFamilies

/-! # An explicit finite exceptional divisor for joint factorial-gap observations -/

namespace Erdos478.LocalWitness
open Polynomial Finset SplittingDensity
noncomputable section

def exceptionalFactor (k : ℕ) :=
  ((gapPoly k).resultant (gapPoly k).derivative).natAbs * (k.factorial-1)

def exceptionalProduct (S : Finset ℕ) := ∏ k∈S, exceptionalFactor k

theorem resultant_ne {f : ℤ[X]} (hs : (f.map (Int.castRingHom ℚ)).Separable) :
    f.resultant f.derivative≠0 := by
  let ι := Int.castRingHom ℚ
  have hin : Function.Injective ι := Int.cast_injective
  intro zero
  have h := congrArg ι zero
  rw [← resultant_map_map,map_zero] at h
  have cop : IsCoprime (f.map ι) (f.derivative.map ι) := by rw [← derivative_map]; exact hs
  exact resultant_ne_zero _ _ cop (by simpa only [natDegree_map_eq_of_injective hin] using h)

theorem exceptionalProduct_pos (S : Finset ℕ) (hs : ∀ k∈S, 2≤k) : 0<exceptionalProduct S := by
  apply prod_pos
  intro k hk
  have hk₂ := hs k hk
  have pos : 0<k := by omega
  have sep : ((gapPoly k).map (Int.castRingHom ℚ)).Separable := by
    simpa [gapPoly] using (GapFamilies.irreducible_gap_rat pos).separable
  exact Nat.mul_pos (Int.natAbs_pos.mpr (resultant_ne sep))
    (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hk₂))

theorem separable_of_regular {f : ℤ[X]} (hd : f.natDegree≠0) (p : ℕ) [Fact p.Prime]
    (good : ¬p∣(f.resultant f.derivative).natAbs) : (f.map (Int.castRingHom (ZMod p))).Separable := by
  let D := f.resultant f.derivative
  let φ := Int.castRingHom (ZMod p)
  have nonzero : φ D≠0 := fun h => good (Int.ofNat_dvd_left.mp ((CharP.intCast_eq_zero_iff _ p D).mp h))
  obtain ⟨u,v,_,_,bezout⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl le_rfl (Or.inl hd)
  have eq := congrArg (Polynomial.map φ) bezout
  change (f*u+f.derivative*v).map φ=(C D).map φ at eq
  simp only [Polynomial.map_add,Polynomial.map_mul,map_C,← derivative_map] at eq
  refine ⟨C (φ D)⁻¹*u.map φ,C (φ D)⁻¹*v.map φ,?_⟩
  calc
    _ = C (φ D)⁻¹*(f.map φ*u.map φ+(f.map φ).derivative*v.map φ) := by ring
    _ = 1 := by rw [eq,← C_mul,inv_mul_cancel₀ nonzero,C_1]

theorem regular_gap {p k : ℕ} [hpr : Fact p.Prime] {S : Finset ℕ} (hk : k∈S) (hk₂ : 2≤k)
    (good : ¬p∣exceptionalProduct S) :
    ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable ∧ k.factorial%p≠1 := by
  have ng : ¬p∣exceptionalFactor k := fun h => good (h.trans (dvd_prod_of_mem exceptionalFactor hk))
  have disc : ¬p∣((gapPoly k).resultant (gapPoly k).derivative).natAbs := fun h => ng (dvd_mul_of_dvd_left h _)
  have bdy : ¬p∣k.factorial-1 := fun h => ng (dvd_mul_of_dvd_right h _)
  have pos : 0<k := by omega
  refine ⟨separable_of_regular ((gap_degree pos).natDegree_eq.trans_ne pos.ne') p disc,fun he => ?_⟩
  apply bdy
  apply (Nat.modEq_iff_dvd' (Nat.factorial_pos k)).mp
  change 1%p=k.factorial%p
  rw [he,Nat.mod_eq_of_lt hpr.out.one_lt]

#print axioms exceptionalFactor
#print axioms exceptionalProduct
#print axioms resultant_ne
#print axioms exceptionalProduct_pos
#print axioms separable_of_regular
#print axioms regular_gap
end
end Erdos478.LocalWitness
