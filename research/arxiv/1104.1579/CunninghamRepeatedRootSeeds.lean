import CunninghamSharedFactorTable
import CunninghamLinearCyclotomicFactors

/-! The seed conditions forced by a repeated root, including roots of unity. -/

namespace CunninghamChain.SharedFactors
open Polynomial LinearRoots

/-- The five affine lines and two isolated seeds where an irreducible factor repeats. -/
def ExceptionalSeed (a b : ℤ) : Prop :=
  b=a ∨ b=a+1 ∨ b=a-1 ∨ a-2*b=4 ∨ a-2*b= -4 ∨ (a=1 ∧ b= -1) ∨ (a=2 ∧ b=0)

private lemma same_sign_distinct {k : Bool} {a b : ℤ} {z : ℂ} (hu : OffUnity z)
    {m n : ℕ} (hlt : m<n) (h₁ : aeval z (term k a b m)=0)
    (h₂ : aeval z (term k a b n)=0) : False := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have h1 : z ≠ 1 := by simpa using hu 1 (by decide)
  have e := (root_equation k a b m z h1).mp h₁
  have f := (root_equation k a b (m+s) z h1).mp h₂
  rw [pow_add] at f
  apply hu s (by omega)
  cases k
  · norm_num [sign] at e f
    linear_combination -(f - z^s*e)
  · norm_num [sign] at e f
    linear_combination -(z^s*e - f)

private lemma opposite_same_index {k : Bool} {a b : ℤ} {z : ℂ} (hu : OffUnity z)
    {m : ℕ} (hm : 0 < m) (h₁ : aeval z (term k a b m)=0)
    (h₂ : aeval z (term (!k) a b m)=0) : False := by
  have h1 : z ≠ 1 := by simpa using hu 1 (by decide)
  have e := (root_equation k a b m z h1).mp h₁
  have f := (root_equation (!k) a b m z h1).mp h₂
  apply hu m hm
  cases k
  · norm_num [sign] at e f
    linear_combination (f-e)/2
  · norm_num [sign] at e f
    linear_combination (e-f)/2

private lemma exceptional_of_unity {a b : ℤ} (ha : 0 < a) {k l : Bool} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hne : k≠l ∨ m≠n) {z : ℂ} (hu : ¬ OffUnity z)
    (h₁ : aeval z (term k a b m)=0) (h₂ : aeval z (term l a b n)=0) : ExceptionalSeed a b := by
  unfold OffUnity at hu
  push Not at hu
  obtain ⟨d,hd,hpow⟩ := hu
  let t := orderOf z
  have ht : 0 < t := Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hpow) hd
  have hz : IsPrimitiveRoot z t := IsPrimitiveRoot.orderOf z
  have hA := (primitive_dvd ht hz _).mpr h₁
  have hB := (primitive_dvd ht hz _).mpr h₂
  by_cases h : t=1
  · rw [h] at hA hB
    have A := (linear_cyclotomic_endpoints ..).1.mp hA
    have B := (linear_cyclotomic_endpoints ..).1.mp hB
    cases k <;> cases l <;> norm_num [sign] at A B hne <;> omega
  by_cases h' : t=2
  · rw [h'] at hA
    have A := (linear_cyclotomic_endpoints ..).2.mp hA
    unfold ExceptionalSeed
    split_ifs at A <;> cases k <;> norm_num [sign] at A <;> omega
  have A := ((higher_cyclotomic_iff ha m t (by omega)).mp hA).2
  unfold ExceptionalSeed
  rcases A with h|h|h|h|h <;> omega

/-- Roots outside the roots of unity must occur at opposite signs and distinct indices. -/
theorem off_unity_rows {a b : ℤ} (ha : 0 < a) {k l : Bool} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hne : k≠l ∨ m≠n) {z : ℂ} (hu : OffUnity z)
    (h₁ : aeval z (term k a b m)=0) (h₂ : aeval z (term l a b n)=0) :
    CollisionRow k a b m n z ∨ CollisionRow l a b n m z := by
  wlog hmn : m ≤ n generalizing k l m n
  · exact (this hn hm (hne.imp Ne.symm Ne.symm) h₂ h₁ (by omega)).symm
  by_cases hkl : k=l
  · subst l
    exact (same_sign_distinct hu (lt_of_le_of_ne hmn (hne.resolve_left (by simp))) h₁ h₂).elim
  have he : l=(!k) := by cases l <;> cases k <;> simp_all
  subst l
  rcases eq_or_lt_of_le hmn with rfl|hlt
  · exact (opposite_same_index hu hm h₁ h₂).elim
  exact Or.inl ((common_root_iff_row ha hm hlt hu).mp ⟨h₁,h₂⟩)

lemma CollisionRow.exceptional {k : Bool} {a b : ℤ} {m n : ℕ} {z : ℂ}
    (h : CollisionRow k a b m n z) :
    a-2*b=4 ∨ a-2*b= -4 ∨ (a=2 ∧ (b=0 ∨ b=1 ∨ b=2)) := by
  rcases h with h|h|h|h <;> cases k <;> simp [sign] at h <;> omega

/-- A common root at distinct positive signed indices forces an exceptional seed. -/
theorem exceptional_of_shared_root {a b : ℤ} (ha : 0 < a) {k l : Bool} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hne : k≠l ∨ m≠n) {z : ℂ}
    (h₁ : aeval z (term k a b m)=0) (h₂ : aeval z (term l a b n)=0) : ExceptionalSeed a b := by
  by_cases hu : OffUnity z
  · rcases off_unity_rows ha hm hn hne hu h₁ h₂ with h|h <;>
      have := h.exceptional <;> unfold ExceptionalSeed <;> omega
  · exact exceptional_of_unity ha hm hn hne hu h₁ h₂

#print axioms off_unity_rows
#print axioms exceptional_of_shared_root

end CunninghamChain.SharedFactors
