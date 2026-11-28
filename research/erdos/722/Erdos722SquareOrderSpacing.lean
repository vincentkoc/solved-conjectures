import Erdos722InversiveOrder

/-!
# A gap above the square boundary

Write v=q²+1+(q−1)d. For every prime p dividing q, the point and
pair replication numbers force d to be 0 or −1 modulo p.
-/

namespace Erdos722.InversiveOrder
open Finset IntegralDesign MinimumOrder

private theorem twice_choose (a : ℕ) : 2*a.choose 2=(a-1)*a := by
  change Nat.factorial 2*_ = _
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.descFactorial_succ]

theorem square_order_spacing {v q p : ℕ} (hq : 2≤q) (hp : p.Prime) (hpq : p∣q)
    (hv : q^2+1<v) (ht : ∀ i<3, (q+1-i).choose (3-i) ∣ (v-i).choose (3-i)) :
    ∃ d : ℕ, 0<d ∧ v=q^2+1+(q-1)*d ∧ (p∣d ∨ p∣d+1) := by
  have hq₁ : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hprod : (q-1)*(q+1)+1=q^2 := by
    nlinarith only [congrArg (·*(q+1)) hq₁,hq₁]
  have hv₂ : 2≤v := by omega
  have hq₂ : q+1-2=q-1 := by omega
  obtain ⟨a,ha⟩ := ht 2 (by decide)
  norm_num only [show 3-2=1 by decide,Nat.choose_one_right,hq₂] at ha
  have hlt : (q-1)*(q+1)<(q-1)*a := by omega
  have ha' := Nat.lt_of_mul_lt_mul_left hlt
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ha'.le
  rw [hd,mul_add] at ha
  have he : v=q^2+1+(q-1)*d := by omega
  refine ⟨d,by omega,he,?_⟩
  have hnd : ¬p∣q-1 := by
    intro h
    have : p∣q-(q-1) := Nat.dvd_sub hpq h
    rw [show q-(q-1)=1 by omega] at this
    exact hp.not_dvd_one this
  obtain ⟨j,hj⟩ := ht 1 (by decide)
  norm_num only [show 3-1=2 by decide,Nat.add_sub_cancel] at hj
  have hb : (v-2)*(v-1)=(q-1)*q*j := by
    calc
      _ = 2*(v-1).choose 2 := by rw [twice_choose]; rfl
      _ = 2*(q.choose 2*j) := congrArg (2*·) hj
      _ = _ := by rw [← mul_assoc,twice_choose]
  have hdiv : p∣(v-2)*(v-1) := hb ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpq _) _
  rcases hp.dvd_mul.mp hdiv with h|h
  · right
    rw [← mul_add,← hd] at ha
    have hh : p∣a := (hp.dvd_mul.mp (ha ▸ h)).resolve_left hnd
    rw [hd,show q+1+d=q+(d+1) by omega] at hh
    exact (Nat.dvd_add_right hpq).mp hh
  · left
    have hh : v-1=q^2+(q-1)*d := by omega
    have hqpow : p∣q^2 := hpq.trans (dvd_pow_self _ (by decide))
    exact (hp.dvd_mul.mp ((Nat.dvd_add_right hqpow).mp (hh ▸ h))).resolve_left hnd

/-- If the first two possible geometric orders fail, a large prime
factor of q gives a further gap of (q−1)(p−1) above q²+1. -/
theorem prime_gap_of_no_plane {v q p : ℕ} (hq : 3<q) (h₅ : q≠5) (h₁₁ : q≠11)
    (hp : p.Prime) (hpq : p∣q) (hn : ¬PlaneOfOrder q) (hv : q+1<v)
    {H : Finset (Finset (Fin v))} (hH : H.IsBlockDesign 3 (q+1)) :
    q^2+1+(q-1)*(p-1)≤v := by
  have hl := triple_square_lower (by omega : 3<q+1) hv (by omega) (by omega) (by omega) hH
  simp only [Nat.add_sub_cancel] at hl
  have hne : v≠q^2+1 := by
    rintro rfl
    exact hn (plane_of_square_design (by omega) 1 hH)
  have ht := (signed_steiner_iff v 3 (q+1) (by omega) hv.le).mp ⟨_,design_weights hH⟩
  obtain ⟨d,hd,he,hm⟩ := square_order_spacing (by omega) hp hpq (by omega) ht
  have hd' : p-1≤d := by
    rcases hm with h|h
    · have := Nat.le_of_dvd hd h
      omega
    · have := Nat.le_of_dvd (by omega : 0<d+1) h
      omega
  exact he ▸ Nat.add_le_add_left (Nat.mul_le_mul_left _ hd') _

#print axioms square_order_spacing
#print axioms prime_gap_of_no_plane
end Erdos722.InversiveOrder
