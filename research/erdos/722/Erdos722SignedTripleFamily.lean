import Erdos722SignedSteinerObstruction

/-!
# An infinite family of signed 3-designs without Steiner realizations

Write m = 2t+4 and k = 2m−1. The order v = (k−2)m+2 has all the
divisibilities for S(3,k,v). Each pair would lie in m blocks, whereas
an exterior point forces at least k−1. Both the order and block size grow.
-/

namespace Erdos722.IntegralDesign
open Finset

private theorem choose_multiple {u v i d : ℕ} (h : u.descFactorial i=v.descFactorial i*d) :
    u.choose i=v.choose i*d := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos i)
  rwa [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc] at h

/-- The successive replication numbers required at levels 0, 1, 2 are
(t+2)v, (t+2)k and 2t+4. -/
theorem triple_family_divisibility (t : ℕ) :
    let k := 4*t+7
    let v := (4*t+5)*(2*t+4)+2
    ∀ i<3, (k-i).choose (3-i) ∣ (v-i).choose (3-i) := by
  intro k v i hi
  let h := (4*t+5)*(2*t+4)
  have hv₁ : v-1=h+1 := rfl
  have hv₂ : v-2=h := by dsimp [v,h]; omega
  have hk₁ : k-1=4*t+6 := rfl
  have hk₂ : k-2=4*t+5 := by dsimp [k]; omega
  interval_cases i
  · refine ⟨(t+2)*v,choose_multiple ?_⟩
    simp only [Nat.sub_zero,Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one,hv₁,hv₂,hk₁,hk₂]
    dsimp [v,k,h]
    ring
  · refine ⟨(t+2)*k,choose_multiple ?_⟩
    norm_num only [show 3-1=2 by decide,Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one,Nat.sub_zero,Nat.sub_sub]
    rw [hv₁,hv₂,hk₁,hk₂]
    dsimp [k,h]
    ring
  · refine ⟨2*t+4,?_⟩
    norm_num [hv₂,hk₂,h]

/-- Every parameter in this sequence has signed index one and fails the
canonical ordinary Steiner predicate. -/
theorem triple_signed_separation (t : ℕ) :
    let k := 4*t+7
    let v := (4*t+5)*(2*t+4)+2
    (∃ w, Represents (univ : Finset (Fin v)) 3 k (fun _ => 1) w) ∧
      ¬∃ H : Finset (Finset (Fin v)), H.IsBlockDesign 3 k := by
  intro k v
  have hk : 3≤k := by dsimp [k]; omega
  have hv : k<v := by dsimp [k,v]; nlinarith [Nat.zero_le (t*t),Nat.zero_le t]
  refine ⟨(signed_steiner_iff v 3 k hk hv.le).mpr (triple_family_divisibility t),?_⟩
  rintro ⟨H,hH⟩
  have h := exterior_point_bound (s:=1) hk hv hH
  have k₁ : k-1=4*t+6 := rfl
  have k₂ : k-(1+1)=4*t+5 := by dsimp [k]; omega
  have nv : v-(1+1)=(4*t+5)*(2*t+4) := by dsimp [v]; omega
  rw [k₁,k₂,nv] at h
  have := Nat.le_of_mul_le_mul_left h (by omega)
  omega

/-- Any eventual-existence cutoff in the host's quantifier order must exceed
the displayed quadratic order at these block sizes. -/
theorem triple_cutoff_lower_bound (t N : ℕ)
    (h : ∀ n≥N, (∀ i<3, (4*t+7-i).choose (3-i) ∣ (n-i).choose (3-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 (4*t+7)) :
    (4*t+5)*(2*t+4)+2 < N := by
  by_contra! hu
  exact (triple_signed_separation t).2 (h _ hu (triple_family_divisibility t))

#print axioms triple_cutoff_lower_bound
#print axioms triple_family_divisibility
#print axioms triple_signed_separation
end Erdos722.IntegralDesign
