import Erdos722LargePairIndex
import Erdos722IndexUnfolding
import Erdos722CyclotomicSpectrum
import Erdos722AffineIngredients

/-!
# Ordinary pair designs in every admissible residue class

Unfold an admissible starting order at prime index congruent to one
modulo the desired modulus. This also supplies every admissible group
count residue needed by the interval construction.
-/

namespace Erdos722.PairUnfolding
open Finset Filter Erdos722.Quartet

/-- Every admissible residue represented by a sufficiently large order contains
arbitrarily large orders of ordinary Steiner pair designs. -/
theorem residue_lifts {v k : ℕ} (hk : 2≤k) (hv : k+2≤v)
    (h₁ : k-1 ∣ v-1) (h₂ : k.choose 2 ∣ v.choose 2) (M : ℕ) (hM : 0<M) :
    ∃ᶠ n : ℕ in atTop, n ≡ v [MOD M] ∧ Has (·=k) n := by
  classical
  obtain ⟨L,hL⟩ := PairLattice.eventual_index (α:=Fin v) hk (by simpa using hv)
  let P := M*(k*(k-1))
  have hK : 0<k*(k-1) := Nat.mul_pos (by omega) (by omega)
  have hP : 0<P := Nat.mul_pos hM hK
  let d := Fintype.card (Coord v)
  have hd : 0<d := Fintype.card_pos_iff.mpr
    ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0 : ℕ)<1; decide⟩⟩
  rw [frequently_atTop]
  intro B
  obtain ⟨q,hq,hqN,hm⟩ := Nat.exists_prime_gt_modEq_one (max B (max v (max L (Cyclotomy.cutoff k)))) hP.ne'
  have hqB : B≤q := by omega
  have hvq : v<q := by omega
  have hLq : L≤q := by omega
  have hbig : Cyclotomy.cutoff k<q := by omega
  have hpow : q≤q^d := Nat.le_self_pow hd.ne' q
  have hqq : IsPrimePow (q^d) := (isPrimePow_nat_iff _).mpr ⟨q,d,hq,hd,rfl⟩
  have hqk : q ≡ 1 [MOD k*(k-1)] := hm.of_dvd (dvd_mul_left _ _)
  have hqm : q ≡ 1 [MOD M] := hm.of_dvd (dvd_mul_right _ _)
  have Hq : q^d ≡ 1 [MOD k*(k-1)] := by simpa using hqk.pow d
  have hpos : 1≤q^d := hq.one_le.trans hpow
  obtain ⟨H,hH⟩ := Cyclotomy.prime_power_design hqq hk (hbig.trans_le hpow)
    ((Nat.modEq_iff_dvd' hpos).mp Hq.symm)
  obtain ⟨w,hw⟩ := hL q hLq (by simpa using dvd_mul_of_dvd_right h₁ q)
    (by simpa using dvd_mul_of_dvd_right h₂ q)
  refine ⟨v*q^d,hqB.trans (hpow.trans (Nat.le_mul_of_pos_left _ (by omega))),?_,?_⟩
  · simpa using (hqm.pow d).mul_left v
  · exact lift_at_prime hq hvq w hw ⟨Cover.ofDesign hH⟩

#print axioms residue_lifts
end Erdos722.PairUnfolding

namespace Erdos722.PairDesign
open Finset Filter Erdos722.Quartet

def Allowed (k u : ℕ) := k ∣ ((k-1)*u+1)*u

theorem allowed_congr {k u v : ℕ} (h : u ≡ v [MOD k]) : Allowed k u ↔ Allowed k v :=
  (((h.mul_left (k-1)).add_right 1).mul h).dvd_iff (dvd_refl k)

private theorem twice_pairs (n : ℕ) : n.choose 2*2=n*(n-1) := by
  rw [Nat.choose_two_right,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]

theorem allowed_iff_pairs {k u : ℕ} (hk : 2≤k) :
    Allowed k u ↔ k.choose 2 ∣ ((k-1)*u+1).choose 2 := by
  calc
    Allowed k u ↔ (k-1)*k ∣ (k-1)*(((k-1)*u+1)*u) :=
      (Nat.mul_dvd_mul_iff_left (by omega : 0<k-1)).symm
    _ ↔ k.choose 2*2 ∣ ((k-1)*u+1).choose 2*2 := by
      rw [twice_pairs,twice_pairs]
      simp only [Nat.add_one_sub_one,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
    _ ↔ _ := Nat.mul_dvd_mul_iff_right (by decide : 0<2)

/-- A design in every admissible group-count class modulo a multiple of k. -/
theorem residue_seed {k s : ℕ} (hk : 2≤k) (hs : 0<s) (hks : k∣s) (r : ℕ) (hr : Allowed k r) :
    ∃ x, x ≡ r [MOD s] ∧ Local k x := by
  let j := r+s*(k+2)
  let v := (k-1)*j+1
  have hj : j ≡ r [MOD s] := by
    simp [j]
  have hallow := (allowed_congr (hj.of_dvd hks)).mpr hr
  have hjbig : k+2≤j := by
    have := Nat.le_mul_of_pos_left (k+2) hs
    dsimp [j]; omega
  have hvbig : k+2≤v := by
    have := Nat.le_mul_of_pos_left j (by omega : 0<k-1)
    dsimp [v]; omega
  have h₁ : k-1 ∣ v-1 := by simp [v]
  have h₂ : k.choose 2 ∣ v.choose 2 := (allowed_iff_pairs hk).mp hallow
  have lift := PairUnfolding.residue_lifts hk hvbig h₁ h₂ ((k-1)*s) (Nat.mul_pos (by omega) hs)
  obtain ⟨n,hn,hm,H⟩ := frequently_atTop.mp lift v
  obtain ⟨z,hz⟩ := (Nat.modEq_iff_dvd' hn).mp hm.symm
  refine ⟨j+s*z,?_,?_⟩
  · exact (show j+s*z ≡ j [MOD s] by simp).trans hj
  · change Has (·=k) ((k-1)*(j+s*z)+1)
    have he : v+(k-1)*s*z=n := by omega
    rwa [show (k-1)*(j+s*z)+1=n by rw [← he]; dsimp [v]; ring]

#print axioms allowed_iff_pairs
#print axioms residue_seed
end Erdos722.PairDesign
