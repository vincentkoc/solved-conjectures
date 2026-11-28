import Mathlib

/-!
# The local density in a finite polynomial sieve

Once the primes up to the degree have been cleared, at most `D` forbidden
residues per prime leave a density bounded below solely in terms of the number
of excluded primes. The estimate holds for distinct integer moduli as well.
-/

namespace Erdos478.SchurSieve
open Finset

theorem local_mass (Q : Finset ℕ) (D : ℕ) (ν : ℕ → ℕ)
    (hQ : ∀ q ∈ Q, D < q) (hν : ∀ q ∈ Q, ν q ≤ D) :
    1 ≤ ((Q.card+1 : ℕ) : ℝ)^D * ∏ q ∈ Q, (1 - (ν q : ℝ)/q) := by
  classical
  induction Q using Finset.induction_on_max with
  | empty => simp
  | insert q T hmax ih =>
    have hq : D < q := hQ q (mem_insert_self ..)
    have hqt : q ∉ T := fun h => (lt_irrefl q) (hmax q h)
    have hT : ∀ t ∈ T, D < t := fun t ht => hQ t (mem_insert_of_mem ht)
    have hνT : ∀ t ∈ T, ν t ≤ D := fun t ht => hν t (mem_insert_of_mem ht)
    have hcard := card_le_card (show T ⊆ Ioo D q from fun t ht => mem_Ioo.mpr ⟨hT t ht,hmax t ht⟩)
    rw [Nat.card_Ioo] at hcard
    have hnat : T.card + 1 ≤ q-D := by omega
    let c : ℝ := T.card+1
    have hc : 0<c := by dsimp [c]; positivity
    have hp : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
    have hD : c ≤ (q:ℝ)-D := by apply (le_sub_iff_add_le).mpr; dsimp [c]; exact_mod_cast (show T.card+1+D ≤ q by omega)
    have hνq : (ν q : ℝ) ≤ D := by exact_mod_cast hν q (mem_insert_self ..)
    have hb := one_add_mul_le_pow (a := (1:ℝ)/c) (by linarith [one_div_pos.mpr hc] : -(2:ℝ) ≤ 1/c) D
    have hinv : (q:ℝ) ≤ (q-(ν q : ℝ))*(1+D*(1/c)) := by
      have he := mul_le_mul_of_nonneg_right (show c ≤ (q:ℝ)-ν q by linarith) (Nat.cast_nonneg D : 0 ≤ (D:ℝ))
      field_simp [hc.ne']; nlinarith
    have hlocal : 1 ≤ (1 - (ν q : ℝ)/q)*(1+1/c)^D := by
      calc
        1 = (q:ℝ)/q := (div_self hp.ne').symm
        _ ≤ ((q-(ν q : ℝ))*(1+1/c)^D)/q := (div_le_div_iff_of_pos_right hp).mpr
          (hinv.trans (mul_le_mul_of_nonneg_left hb (by linarith)))
        _ = _ := by field_simp
    have hfactor : c^D ≤ (c+1)^D * (1-(ν q : ℝ)/q) := by
      have eq : (c+1)^D = c^D*(1+1/c)^D := by rw [← mul_pow]; congr 1; field_simp
      rw [eq]; nlinarith [mul_le_mul_of_nonneg_left hlocal (pow_nonneg hc.le D)]
    have hprod : 0 ≤ ∏ t ∈ T, (1-(ν t : ℝ)/t) := by
      apply prod_nonneg
      intro t ht
      exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast (show 0<t by have := hT t ht; omega))).mpr
        (by exact_mod_cast (hνT t ht).trans (hT t ht).le))
    rw [card_insert_of_notMem hqt,prod_insert hqt]
    push_cast
    apply (ih hT hνT).trans
    dsimp [c] at hfactor
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using mul_le_mul_of_nonneg_right hfactor hprod

/-- Total CRT discrepancy after truncating inclusion-exclusion at degree `m`. -/
theorem truncation_error (Q : Finset ℕ) (ν : ℕ → ℕ) (D m : ℕ)
    (hν : ∀ q ∈ Q, ν q ≤ D) :
    (∑ j ∈ range (m+1), ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ν q) ≤
      (m+1)*((Q.card+1)*(D+1))^m := by
  classical
  have hsum (j : ℕ) : (∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ν q) ≤ (Q.card * D)^j := by
    calc
      _ ≤ ∑ _T ∈ Q.powersetCard j, D^j := by
        apply sum_le_sum
        intro T hT
        obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hT
        simpa [hcard] using prod_le_prod' (s := T) (fun q hq => hν q (hsub hq))
      _ = Q.card.choose j * D^j := by simp
      _ ≤ Q.card^j * D^j := Nat.mul_le_mul_right _ (Nat.choose_le_pow ..)
      _ = _ := (mul_pow ..).symm
  calc
    _ ≤ ∑ _j ∈ range (m+1), ((Q.card+1)*(D+1))^m := by
      apply sum_le_sum
      intro j hj
      apply (hsum j).trans
      calc
        _ ≤ ((Q.card+1)*(D+1))^j := Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) _
        _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by simpa using hj)
    _ = _ := by simp

#print axioms local_mass
#print axioms truncation_error

end Erdos478.SchurSieve
