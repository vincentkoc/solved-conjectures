import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic

/-!
# Replication numbers for Steiner triples of points in blocks of size q+1

At orders above the inversive-plane order, a prime-power q leaves two
possible values of the order modulo q(q−1). Both give the same remaining
divisibility test on the quotient.
-/

namespace Erdos722.SecondOrder

/-- The three binomial conditions in the pinned rank-three statement. -/
def Tests (q v : ℕ) := ∀ i<3, (q+1-i).choose (3-i) ∣ (v-i).choose (3-i)

/-- The remaining divisibility test after the pair and point replications. -/
def testValue (z : ℕ) := 2*z*(z+1)*(2*z+1)

private theorem desc_test (u v k : ℕ) :
    u.choose k ∣ v.choose k ↔ u.descFactorial k ∣ v.descFactorial k := by
  simp only [Nat.descFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_dvd_mul_iff_left (Nat.factorial_pos k)).symm

private theorem pair_test {q v m : ℕ} (hq : 2≤q) (hv : 2≤v) (hm : v-2=(q-1)*m) :
    q.choose 2 ∣ (v-1).choose 2 ↔ q ∣ (v-1)*m := by
  rw [desc_test]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
  rw [show v-1-1=v-2 by omega,hm,mul_assoc,mul_comm m (v-1)]
  exact Nat.mul_dvd_mul_iff_left (by omega : 0<q-1)

private theorem full_test {q v m b : ℕ} (hq : 2≤q) (hv : 3≤v)
    (hm : v-2=(q-1)*m) (hb : (v-1)*m=q*b) :
    Tests q v ↔ q+1 ∣ v*b := by
  have ht : (q+1).choose 3 ∣ v.choose 3 ↔ q+1 ∣ v*b := by
    rw [desc_test]
    simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,mul_one,
      show q+1-2=q-1 by omega,Nat.add_sub_cancel]
    have eq : (v-2)*((v-1)*v)=((q-1)*q)*(v*b) := by rw [hm]; nlinarith only [congrArg ((q-1)*v*·) hb]
    rw [eq,← mul_assoc]
    exact Nat.mul_dvd_mul_iff_left (Nat.mul_pos (by omega) (by omega))
  constructor
  · intro h
    exact ht.mp (by simpa using h 0 (by decide))
  · intro h i hi
    interval_cases i
    · simpa using ht.mpr h
    · simpa using (pair_test hq (by omega) hm).mpr ⟨b,hb⟩
    · simpa [show q+1-2=q-1 by omega] using (show q-1∣v-2 from ⟨m,hm⟩)

private theorem q_cast (q : ℕ) : (q : ZMod (q+1))= -1 := by
  have h := ZMod.natCast_self (q+1)
  push_cast at h
  linear_combination h

private theorem test_mod (q z u : ℕ)
    (h : (u : ZMod (q+1))=(testValue z : ℕ)) : q+1∣u ↔ q+1∣testValue z := by
  rw [← ZMod.natCast_eq_zero_iff,← ZMod.natCast_eq_zero_iff,h]

/-- The first order form has pair replication qz. -/
theorem first_form {q z : ℕ} (hq : 2≤q) (hz : 0<z) :
    Tests q (q*(q-1)*z+2) ↔ q+1∣testValue z := by
  let v := q*(q-1)*z+2
  have hm : v-2=(q-1)*(q*z) := by dsimp [v]; rw [Nat.add_sub_cancel]; ring
  have hb : (v-1)*(q*z)=q*((v-1)*z) := by ring
  have hv : 3≤v := by
    have h₁ : 0<q-1 := by omega
    have h₂ : 0<q := by omega
    have h₃ : 0<q*(q-1)*z := by positivity
    dsimp [v]
    omega
  change Tests q v ↔ _
  rw [full_test hq hv hm hb]
  apply test_mod
  dsimp [v,testValue]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_sub (by omega : 1≤q),Nat.cast_one,Nat.cast_ofNat,q_cast]
  ring

/-- The other order form has pair replication qz+q+1. -/
theorem second_form {q z : ℕ} (hq : 2≤q) :
    Tests q (q*(q-1)*z+q^2+1) ↔ q+1∣testValue z := by
  let v := q*(q-1)*z+q^2+1
  have hq' : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hv : 3≤v := by dsimp [v]; nlinarith [Nat.zero_le (q*(q-1)*z),Nat.mul_self_le_mul_self hq]
  have hm : v-2=(q-1)*(q*z+q+1) := by
    have h : v=(q-1)*(q*z+q+1)+2 := by dsimp [v]; nlinarith only [hq',congrArg (q*·) hq']
    omega
  have hb : (v-1)*(q*z+q+1)=q*(((q-1)*z+q)*(q*z+q+1)) := by
    dsimp [v]; ring
  change Tests q v ↔ _
  rw [full_test hq hv hm hb]
  apply test_mod
  dsimp [v,testValue]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_sub (by omega : 1≤q),
    Nat.cast_one,Nat.cast_ofNat,q_cast]
  ring


/-- A prime power dividing a product of coprime natural numbers divides a factor. -/
theorem primary_dvd {q a b : ℕ} (hq : IsPrimePow q) (hab : a.Coprime b)
    (h : q∣a*b) : q∣a ∨ q∣b := by
  obtain ⟨p,l,hp,_,rfl⟩ := (isPrimePow_nat_iff _).mp hq
  by_cases ha : p∣a
  · exact Or.inl (((Nat.Coprime.of_dvd_left ha hab).pow_left l).dvd_of_dvd_mul_right h)
  · exact Or.inr (((hp.coprime_iff_not_dvd.mpr ha).pow_left l).dvd_of_dvd_mul_left h)

/-- Above q²+1 the host binomial tests give exactly two forms with a common test. -/
theorem order_forms {v q : ℕ} (hp : IsPrimePow q) (hq : 2≤q) (hv : q^2+1<v) :
    Tests q v ↔ ∃ z : ℕ, 0<z ∧ q+1∣testValue z ∧
      (v=q*(q-1)*z+2 ∨ v=q*(q-1)*z+q^2+1) := by
  constructor
  · intro ht
    have hq' : q-1+1=q := Nat.sub_add_cancel (by omega)
    have hbase : (q-1)*(q+1)+2=q^2+1 := by nlinarith only [hq',congrArg (q*·) hq']
    have hv₂ : 2≤v := by omega
    obtain ⟨m,hm⟩ := ht 2 (by decide)
    norm_num only [show 3-2=1 by decide,Nat.choose_one_right,show q+1-2=q-1 by omega] at hm
    have hm' : q+1<m := Nat.lt_of_mul_lt_mul_left (show (q-1)*(q+1)<(q-1)*m by omega)
    have hpair := (pair_test hq hv₂ hm).mp (by simpa using ht 1 (by decide))
    have mm : m-1+1=m := Nat.sub_add_cancel (by omega)
    have hv₁ : v-1=(q-1)*m+1 := by omega
    have he : (v-1)*m+m*(m-1)=q*m^2 := by
      rw [hv₁]
      nlinarith only [congrArg (·*m^2) hq',congrArg (m*·) mm]
    have hd : q∣m*(m-1) := (Nat.dvd_add_right hpair).mp (he ▸ dvd_mul_right q _)
    have co : m.Coprime (m-1) := by
      have H : (m-1+1).Coprime (m-1) := by simp
      rwa [mm] at H
    rcases primary_dvd hp co hd with ⟨z,hz⟩|⟨t,ht'⟩
    · have hz₀ : 0<z := by by_contra! H; simp [Nat.eq_zero_of_le_zero H] at hz; omega
      have heq : v=q*(q-1)*z+2 := by
        calc v = (q-1)*m+2 := by omega
             _ = _ := by rw [hz]; ring
      exact ⟨z,hz₀,(first_form hq hz₀).mp (heq ▸ ht),Or.inl heq⟩
    · have hlt : 1<t := by
        by_contra! H
        have := Nat.mul_le_mul_left q H
        omega
      obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le hlt.le
      have hz₀ : 0<z := by omega
      have heq : v=q*(q-1)*z+q^2+1 := by
        calc v = (q-1)*(q*(1+z)+1)+2 := by rw [← hz,← ht',mm]; omega
             _ = _ := by nlinarith only [hq',congrArg (q*·) hq']
      exact ⟨z,hz₀,(second_form hq).mp (heq ▸ ht),Or.inr heq⟩
  · rintro ⟨z,hz,ht,rfl|rfl⟩
    · exact (first_form hq hz).mpr ht
    · exact (second_form hq).mpr ht

#print axioms primary_dvd
#print axioms order_forms

#print axioms first_form
#print axioms second_form
end Erdos722.SecondOrder
