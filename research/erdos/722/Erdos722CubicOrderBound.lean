import Erdos722SquareOrderSpacing

/-!
# Cubic divisibility and the least order at block size 2p+1

The first two replication tests give d+e=ph with e∈{0,1}.
Modulo 2p+1 the three factors of the triple test then become three
consecutive positive integers beginning with h+2e.
-/

namespace Erdos722.InversiveOrder
open Finset IntegralDesign MinimumOrder

private theorem triple_modulus {v k : ℕ} (ht : k.choose 3 ∣ v.choose 3) :
    k ∣ (v-2)*((v-1)*v) := by
  obtain ⟨j,hj⟩ := ht
  refine ⟨(k-2)*(k-1)*j,?_⟩
  calc
    _ = v.descFactorial 3 := by simp [Nat.descFactorial_succ]
    _ = k.descFactorial 3*j := by simp only [Nat.descFactorial_eq_factorial_mul_choose,hj,mul_assoc]
    _ = _ := by simp [Nat.descFactorial_succ]; ring

private theorem cubic_residue {p v d e h : ℕ} (hp : 3≤p)
    (hv : v=(2*p)^2+1+(2*p-1)*d) (he : d+e=p*h)
    (hc : (2*p+1).choose 3 ∣ v.choose 3) :
    2*p+1 ∣ (h+2*e)*((h+2*e+1)*(h+2*e+2)) := by
  let b := h+2*e
  have ha : 2*p-1+1=2*p := Nat.sub_add_cancel (by omega)
  have H : (2*p+1)*h+v=(2*p+1)*(2*p-1+d)+(b+2) := by
    dsimp [b]
    nlinarith only [hv,he,ha,congrArg (·*(2*p+1)) ha,congrArg (·*d) ha]
  have hm : v ≡ b+2 [MOD 2*p+1] :=
    (Nat.ModEq.modulus_mul_add (m:=2*p+1) (a:=h) (b:=v)).symm.trans
      (H ▸ Nat.ModEq.modulus_mul_add)
  have hv₂ : 2≤v := by nlinarith [Nat.zero_le ((2*p-1)*d)]
  have hm₁ : v-1 ≡ b+1 [MOD 2*p+1] := by
    simpa using hm.sub_right (by omega : 1≤v) (by omega : 1≤b+2)
  have hm₂ : v-2 ≡ b [MOD 2*p+1] := by
    simpa using hm.sub_right hv₂ (by omega : 2≤b+2)
  exact Nat.modEq_zero_iff_dvd.mp
    ((hm₂.mul (hm₁.mul hm)).symm.trans (Nat.modEq_zero_iff_dvd.mpr (triple_modulus hc)))

/-- For every admissible order above the inversive-plane order the exact
integral inequality bounds v from below by p² times the cube root of 2p+1. -/
theorem cubic_bound_above_square {v p : ℕ} (hp : p.Prime) (hp₃ : 3≤p) (hv : (2*p)^2+1<v)
    (ht : ∀ i<3, (2*p+1-i).choose (3-i) ∣ (v-i).choose (3-i)) :
    p^6*(2*p+1)≤v^3 := by
  obtain ⟨d,hd,he,hm⟩ := square_order_spacing (by omega : 2≤2*p) hp (dvd_mul_left ..) hv ht
  have rep : ∃ h e : ℕ, e≤1 ∧ d+e=p*h := by
    rcases hm with ⟨h,hh⟩|⟨h,hh⟩
    · exact ⟨h,0,by decide,by simpa using hh⟩
    · exact ⟨h,1,by decide,hh⟩
  obtain ⟨h,e,he₁,hh⟩ := rep
  have hpos : 0<h := by
    by_contra! hz
    have : h=0 := by omega
    simp [this] at hh
    omega
  have hc := cubic_residue hp₃ he hh (by simpa using ht 0 (by decide))
  have hprod := Nat.le_of_dvd (by positivity) hc
  have hcube : 2*p+1≤(h+4)^3 := hprod.trans (by
    rw [pow_succ,pow_two,mul_assoc]
    apply Nat.mul_le_mul <;> first | omega | apply Nat.mul_le_mul <;> omega)
  have hl : p^2*(h+4)≤v := by
    have ha : 2*p-1+1=2*p := Nat.sub_add_cancel (by omega)
    have h₁ := Nat.mul_le_mul_left (2*p-1) he₁
    have h₂ := Nat.mul_le_mul_right h (show p+2≤p^2 by nlinarith)
    have h₃ := Nat.mul_le_mul_left (p*(p-1)) (show 1≤h by omega)
    have h₄ : p*(p-1)+p=p^2 := by nlinarith only [congrArg (p*·) (Nat.sub_add_cancel (by omega : 1≤p))]
    nlinarith only [he,ha,hh,h₁,h₂,h₃,h₄,congrArg (·*d) ha,congrArg (·*e) ha,
      congrArg (2*p*·) hh,congrArg (·*h) h₄,hp₃]
  calc
    p^6*(2*p+1) ≤ p^6*(h+4)^3 := Nat.mul_le_mul_left _ hcube
    _ = (p^2*(h+4))^3 := by ring
    _ ≤ v^3 := Nat.pow_le_pow_left hl 3

#print axioms cubic_bound_above_square
end Erdos722.InversiveOrder
