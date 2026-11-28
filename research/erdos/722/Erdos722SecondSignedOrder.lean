import Erdos722PrimePowerOrderForms
import Erdos722SteinerWeights

/-!
# The least signed order above an inversive plane

For every prime power q≥2 the first binomial-admissible order above q²+1 is
q(q−1)z+2, where z is the first solution z≥2 of a cubic congruence.
Every ordinary design above q²+1 satisfies the resulting lower bound.
-/

namespace Erdos722.SecondOrder
open Finset IntegralDesign

private theorem exists_index (q : ℕ) : ∃ z : ℕ, 0<z ∧ q+1∣testValue z :=
  ⟨q+1,by omega,by unfold testValue; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left ..) _) _⟩

/-- First positive solution of the remaining divisibility condition. -/
noncomputable def firstIndex (q : ℕ) : ℕ := Nat.find (exists_index q)

theorem firstIndex_spec (q : ℕ) : 0<firstIndex q ∧ q+1∣testValue (firstIndex q) :=
  Nat.find_spec (exists_index q)

theorem firstIndex_le {q z : ℕ} (hz : 0<z) (h : q+1∣testValue z) : firstIndex q≤z :=
  Nat.find_min' (exists_index q) ⟨hz,h⟩

private theorem start_test (q : ℕ) : q+1∣testValue (max 2 (firstIndex q)) := by
  obtain ⟨hp,hd⟩ := firstIndex_spec q
  by_cases h : 2≤firstIndex q
  · simpa only [max_eq_right h] using hd
  · have eq : firstIndex q=1 := by omega
    rw [eq,show testValue 1=12 by decide] at hd
    rw [eq,show max 2 1=2 by decide,show testValue 2=60 by decide]
    exact hd.trans (by decide)

/-- First order above q²+1 satisfying the rank-three binomial tests.
The maximum handles precisely the small moduli dividing twelve. -/
noncomputable def nextAdmissible (q : ℕ) := q*(q-1)*max 2 (firstIndex q)+2

private theorem next_gt {q : ℕ} (hq : 2≤q) : q^2+1<nextAdmissible q := by
  have h := Nat.mul_le_mul_left (q*(q-1)) (le_max_left 2 (firstIndex q))
  have e : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hsq := Nat.mul_le_mul_left q (show 2≤q from hq)
  unfold nextAdmissible
  nlinarith only [h,congrArg (q*·) e,hsq]

theorem least_admissible {q : ℕ} (hp : IsPrimePow q) (hq : 2≤q) :
    IsLeast {v : ℕ | q^2+1<v ∧ Tests q v} (nextAdmissible q) := by
  have hs : 0<max 2 (firstIndex q) := lt_of_lt_of_le (by decide : 0<2) (le_max_left ..)
  refine ⟨⟨next_gt hq,(first_form hq hs).mpr (start_test q)⟩,?_⟩
  rintro v ⟨hv,ht⟩
  obtain ⟨z,hz,hd,he⟩ := (order_forms hp hq hv).mp ht
  have e : q-1+1=q := Nat.sub_add_cancel (by omega)
  have eq : q*(q-1)+q=q^2 := by nlinarith only [congrArg (q*·) e]
  have qpos : 0<q^2 := pow_pos (by omega) _
  unfold nextAdmissible
  by_cases h : 2≤z
  · have hle := Nat.mul_le_mul_left (q*(q-1)) (max_le h (firstIndex_le hz hd))
    rcases he with rfl|rfl <;> omega
  · have ez : z=1 := by omega
    subst z
    have H := firstIndex_le hz hd
    rw [max_eq_left (by omega : firstIndex q≤2)]
    rcases he with rfl|rfl <;> simp only [mul_one,mul_two] at * <;> omega

theorem least_signed {q : ℕ} (hp : IsPrimePow q) (hq : 2≤q) :
    IsLeast {v : ℕ | q^2+1<v ∧ ∃ w, Represents (univ : Finset (Fin v)) 3 (q+1) (fun _ => 1) w}
      (nextAdmissible q) := by
  have H := least_admissible hp hq
  have eq : ∀ v : ℕ, q^2+1<v → q+1≤v := by
    intro v hv; nlinarith [Nat.mul_le_mul_left q (show 1≤q by omega)]
  refine ⟨⟨H.1.1,(signed_steiner_iff _ _ _ (by omega) (eq _ H.1.1)).mpr H.1.2⟩,?_⟩
  rintro v ⟨hv,hw⟩
  exact H.2 ⟨hv,(signed_steiner_iff _ _ _ (by omega) (eq _ hv)).mp hw⟩

/-- The cubic test gives a superquadratic lower bound uniformly in the prime power. -/
theorem cubic_separation {q v : ℕ} (hp : IsPrimePow q) (hq : 2≤q) (hv : q^2+1<v)
    (ht : Tests q v) : (q*(q-1))^3*(q+1)≤12*(v-2)^3 := by
  obtain ⟨z,hz,hd,he⟩ := (order_forms hp hq hv).mp ht
  have hF : q+1≤testValue z := Nat.le_of_dvd (by dsimp [testValue]; positivity) hd
  have hbound : testValue z≤12*z^3 := by
    dsimp [testValue]
    calc 2*z*(z+1)*(2*z+1) ≤ 2*z*(2*z)*(3*z) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
         _ = _ := by ring
  have hq₂ : 0<q^2 := pow_pos (by omega) _
  have hle : q*(q-1)*z≤v-2 := by rcases he with rfl|rfl <;> omega
  calc
    _ ≤ (q*(q-1))^3*(12*z^3) := Nat.mul_le_mul_left _ (hF.trans hbound)
    _ = 12*(q*(q-1)*z)^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left hle _)


/-- For each multiple C, the next order exceeds Cq² for every prime
power q≥96C³. This is uniform over all orders passing the binomial tests. -/
theorem uniform_separation {q v C : ℕ} (hp : IsPrimePow q) (hq : 2≤q) (hC : 96*C^3≤q)
    (hv : q^2+1<v) (ht : Tests q v) : C*q^2<v := by
  by_contra! hu
  let a := q*(q-1)
  have e : q-1+1=q := Nat.sub_add_cancel (by omega)
  have h₂ := Nat.mul_le_mul_left q hq
  have scale : q^2≤2*a := by dsimp [a]; nlinarith only [congrArg (q*·) e,h₂]
  have ha : 0<a := Nat.mul_pos (by omega) (by omega)
  have bound : v-2≤(2*C)*a := by
    calc v-2 ≤ v := Nat.sub_le ..
         _ ≤ C*q^2 := hu
         _ ≤ C*(2*a) := Nat.mul_le_mul_left _ scale
         _ = _ := by ring
  have last : a^3*(q+1)≤a^3*(96*C^3) := calc
    _ ≤ 12*(v-2)^3 := cubic_separation hp hq hv ht
    _ ≤ 12*((2*C)*a)^3 := Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left bound _)
    _ = _ := by ring
  have small := Nat.le_of_mul_le_mul_left last (pow_pos ha 3)
  omega

#print axioms uniform_separation
#print axioms firstIndex_spec
#print axioms firstIndex_le
#print axioms least_admissible
#print axioms least_signed
#print axioms cubic_separation
end Erdos722.SecondOrder
