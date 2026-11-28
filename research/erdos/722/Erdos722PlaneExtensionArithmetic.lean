import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Arithmetic at the minimum Steiner order

Hughes's restriction on extensions of projective planes comes from the
triple replication number. Higher ranks impose further binomial tests.
-/

namespace Erdos722.MinimumOrder

private theorem six_choose_three (a : ℕ) :
    6 * (a+2).choose 3 = (a+2)*(a+1)*a := by
  change Nat.factorial 3 * _ = _
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.descFactorial_succ]
  ring

/-- In an extension of a projective plane of order q, triple replication
forces q+2 to divide 12. -/
theorem triple_divides_twelve {q : ℕ} (hq : 2 ≤ q)
    (h : (q+2).choose 3 ∣ (q*(q+1)+2).choose 3) : q+2 ∣ 12 := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hq
  let q := 2+s
  let a := q*(q+1)
  change (q+2).choose 3 ∣ (a+2).choose 3 at h
  obtain ⟨b,hb⟩ := h
  have he : (a+2)*(a+1) = (q+2)*b := by
    apply Nat.eq_of_mul_eq_mul_right (show 0<a by dsimp [a,q]; positivity)
    calc
      (a+2)*(a+1)*a = 6*(a+2).choose 3 := (six_choose_three a).symm
      _ = 6*((q+2).choose 3*b) := congrArg (6*·) hb
      _ = (q+2)*b*a := by rw [← Nat.mul_assoc,six_choose_three]; dsimp [a]; ring
  have h₂ : a+2 ≡ 4 [MOD q+2] := by
    rw [show a+2=4+(s+1)*(q+2) by dsimp [a,q]; ring,Nat.add_mul_modulus_modEq_iff]
  have h₁ : a+1 ≡ 3 [MOD q+2] := by
    rw [show a+1=3+(s+1)*(q+2) by dsimp [a,q]; ring,Nat.add_mul_modulus_modEq_iff]
  exact ((h₂.mul h₁).dvd_iff (dvd_refl _)).mp ⟨b,he⟩

private theorem boundary_level {q r j : ℕ} (hj : 0 < j) (hjr : j ≤ r)
    (h : ∀ i < r, (q+(r-1)-i).choose (r-i) ∣ (q*(q+1)+(r-1)-i).choose (r-i)) :
    (q+(j-1)).choose j ∣ (q*(q+1)+(j-1)).choose j := by
  have H := h (r-j) (by omega)
  rwa [show r-(r-j)=j by omega,
    show q+(r-1)-(r-j)=q+(j-1) by omega,
    show q*(q+1)+(r-1)-(r-j)=q*(q+1)+(j-1) by omega] at H

/-- These are exactly the arithmetic possibilities for equality in the
exterior-point bound in rank at least three. -/
theorem equality_divisibilities {q r : ℕ} (hq : 2 ≤ q) (hr : 3 ≤ r) :
    (∀ i < r, (q+(r-1)-i).choose (r-i) ∣ (q*(q+1)+(r-1)-i).choose (r-i)) ↔
      (q=2 ∧ r=3) ∨ (q=4 ∧ (r=3 ∨ r=4 ∨ r=5)) ∨ (q=10 ∧ r=3) := by
  constructor
  · intro h
    have hd := triple_divides_twelve hq (boundary_level (by decide : 0<3) hr h)
    have hle := Nat.le_of_dvd (by decide : 0<12) hd
    have hq' : q=2 ∨ q=4 ∨ q=10 := by
      have : q ≤ 10 := by omega
      interval_cases q <;> omega
    rcases hq' with rfl|rfl|rfl
    · left
      refine ⟨rfl,?_⟩
      by_contra! hn
      have h4 := boundary_level (by decide : 0<4) (by omega : 4≤r) h
      exact (by decide : ¬ ((2+(4-1)).choose 4 ∣ (2*(2+1)+(4-1)).choose 4)) h4
    · right; left
      refine ⟨rfl,?_⟩
      by_contra! hn
      have h6 := boundary_level (by decide : 0<6) (by omega : 6≤r) h
      exact (by decide : ¬ ((4+(6-1)).choose 6 ∣ (4*(4+1)+(6-1)).choose 6)) h6
    · right; right
      refine ⟨rfl,?_⟩
      by_contra! hn
      have h4 := boundary_level (by decide : 0<4) (by omega : 4≤r) h
      exact (by decide : ¬ ((10+(4-1)).choose 4 ∣ (10*(10+1)+(4-1)).choose 4)) h4
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl|rfl|rfl⟩|⟨rfl,rfl⟩) i hi <;> interval_cases i <;> decide

#print axioms triple_divides_twelve
#print axioms equality_divisibilities
end Erdos722.MinimumOrder
