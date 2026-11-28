import Erdos722SecondSignedOrder

/-!
# Evaluating the first index when q+1 is also a prime power

The index is exactly q/2 rounded down. For an odd modulus, the three
factors z, z+1, 2z+1 are pairwise coprime. For a power of two one first
cancels the factor two and then removes the odd factor 2z+1.
-/

namespace Erdos722.SecondOrder

theorem index_upper_half {q : ℕ} (hq : 2≤q) : firstIndex q≤q/2 := by
  apply firstIndex_le (by omega)
  by_cases he : q%2=0
  · have eq : 2*(q/2)+1=q+1 := by omega
    unfold testValue
    rw [eq]
    exact dvd_mul_left ..
  · have eq : q+1=2*(q/2+1) := by omega
    refine ⟨q/2*(2*(q/2)+1),?_⟩
    unfold testValue
    rw [eq]
    ring

private theorem odd_index_lower {q z : ℕ} (hp : IsPrimePow (q+1)) (he : q%2=0)
    (hz : 0<z) (hd : q+1∣testValue z) : q/2≤z := by
  have co₂ : (q+1).Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm
  have cv : testValue z=2*(z*(z+1)*(2*z+1)) := by unfold testValue; ring
  have div := co₂.dvd_of_dvd_mul_left (cv ▸ hd)
  have cop : (z*(z+1)).Coprime (2*z+1) := by
    rw [Nat.coprime_mul_iff_left]
    constructor
    · rw [show 2*z+1=z+(z+1) by omega,Nat.coprime_self_add_right]
      simp
    · rw [show 2*z+1=(z+1)+z by omega,Nat.coprime_self_add_right]
      simp
  rcases primary_dvd hp cop div with h|h
  · rcases primary_dvd hp (by simp : z.Coprime (z+1)) h with h|h
    · have := Nat.le_of_dvd hz h
      omega
    · have := Nat.le_of_dvd (by omega : 0<z+1) h
      omega
  · have := Nat.le_of_dvd (by omega : 0<2*z+1) h
    omega

private theorem even_index_lower {q z : ℕ} (hp : IsPrimePow (q+1)) (hq : 4≤q)
    (he : q%2=1) (hz : 0<z) (hd : q+1∣testValue z) : q/2≤z := by
  obtain ⟨p,l,pp,hl,heq⟩ := (isPrimePow_nat_iff _).mp hp
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le (show 1≤l by omega)
  have h₂ : 2∣p^l := heq ▸ (by omega : 2∣q+1)
  have peq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two pp).mp (Nat.prime_two.dvd_of_dvd_pow h₂)
  subst p
  rw [ha,Nat.add_comm 1 a,pow_succ] at heq
  have ha₀ : 0<a := by
    by_contra! H
    simp [Nat.eq_zero_of_le_zero H] at heq
    omega
  have pm : IsPrimePow (2^a : ℕ) := (isPrimePow_nat_iff _).mpr ⟨2,a,Nat.prime_two,ha₀,rfl⟩
  have cv : testValue z=2*(z*(z+1)*(2*z+1)) := by unfold testValue; ring
  rw [← heq,mul_comm (2^a) 2,cv] at hd
  have div := (Nat.mul_dvd_mul_iff_left (by decide : 0<2)).mp hd
  have co : (2^a).Coprime (2*z+1) := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left a
  rcases primary_dvd pm (by simp : z.Coprime (z+1)) (co.dvd_of_dvd_mul_right div) with h|h
  · have := Nat.le_of_dvd hz h
    omega
  · have := Nat.le_of_dvd (by omega : 0<z+1) h
    omega

theorem firstIndex_eq_half {q : ℕ} (hq : 4≤q) (hp : IsPrimePow (q+1)) :
    firstIndex q=q/2 := by
  apply (index_upper_half (by omega)).antisymm
  obtain ⟨hz,hd⟩ := firstIndex_spec q
  by_cases he : q%2=0
  · exact odd_index_lower hp he hz hd
  · exact even_index_lower hp hq (by omega) hz hd

theorem adjacent_primary_minimum {q : ℕ} (hq : 4≤q) (hp : IsPrimePow q) (hs : IsPrimePow (q+1)) :
    IsLeast {v : ℕ | q^2+1<v ∧ Tests q v} (q*(q-1)*(q/2)+2) := by
  simpa only [nextAdmissible,firstIndex_eq_half hq hs, max_eq_right (by omega : 2≤q/2)]
    using least_admissible hp (by omega)

#print axioms index_upper_half
#print axioms firstIndex_eq_half
#print axioms adjacent_primary_minimum
end Erdos722.SecondOrder
