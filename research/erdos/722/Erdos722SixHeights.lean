import Erdos722SixConsecutiveSeeds
import Erdos722SixDirections
import Erdos722FiveMaster
import Erdos722CyclotomicSpectrum

/-!
# Consecutive heights for truncated transversal designs

One prime order gives a design on `5*m+1` points. Two truncations with
thirty full columns at height `m-1`, using respectively 29 and 30 points
in the last column, give usable group counts `30*m` and `30*m+1`.
-/

namespace Erdos722.Six
open Erdos722.Quartet

theorem grow {s t r a : ℕ} (D : Directions s t) (hs : Local s) (hs' : Local (s+1))
    (hr : r ≤ t) (ha : a ≤ 1) (ht : Local (t+a)) (h : Local (r+a)) :
    Local (s*t+r+a) := by
  have C := Erdos722.Five.truncate_with D hs hs' hr ha (Has.single ht) (Has.single h)
  have H := inflate_uniform (by decide : 0 < 5) C.some (fun _ hi => hi)
  simpa only [Local,Fintype.card_fin,show 5+1=6 by decide] using H

def modulus := Nat.factorial 39

theorem modulus_pos : 0 < modulus := Nat.factorial_pos _
theorem three_dvd_modulus : 3 ∣ modulus := Nat.dvd_factorial (by decide) (by decide)

theorem modular_predecessor {b : ℕ} (hb : 2 ≤ b) (h : modulus ∣ b) :
    Nonempty (Directions 39 (b-1)) := by
  apply Nonempty.intro (modular (by omega) ?_)
  apply Nat.Coprime.of_dvd_left h
  exact (Nat.coprime_self_sub_right (by omega : 1 ≤ b)).mpr (by simp)

def Usable (t : ℕ) := Local t ∧ Nonempty (Directions 39 t)

theorem adjacent_heights (N : ℕ) : ∃ T ≥ N, Usable T ∧ Usable (T+1) := by
  let P := modulus ^ 39
  have hP : 0 < P := pow_pos modulus_pos _
  have hF : modulus ∣ P := dvd_pow_self _ (by decide)
  obtain ⟨q,hq,hbig,hmod⟩ := Nat.exists_prime_gt_modEq_one
    (max (Erdos722.Cyclotomy.cutoff 6) (5*(N+40)+1)) (show 5*P ≠ 0 by positivity)
  obtain ⟨z,hz⟩ := (Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm
  let m := P*z
  have heq : 5*m+1=q := by
    have hh : q-1=5*m := hz.trans (Nat.mul_assoc ..)
    have := hq.pos
    omega
  have hm : N+40 < m := by have := (le_max_right ..).trans_lt hbig; omega
  have hPm : P ∣ m := dvd_mul_right _ _
  have hFm := hF.trans hPm
  have h6 : 6 ∣ m := (Nat.dvd_factorial (by decide) (by decide : 6 ≤ 39)).trans hFm
  have hd : 6*(6-1) ∣ q-1 := by
    rw [← heq,Nat.add_sub_cancel]
    simpa only [show 6*(6-1)=5*6 by decide] using Nat.mul_dvd_mul_left 5 h6
  obtain ⟨H,hH⟩ := Erdos722.Cyclotomy.prime_power_design hq.isPrimePow (by decide : 2≤6)
    ((le_max_left ..).trans_lt hbig) hd
  have seed : Local m := by
    change Has (· = 6) (5*m+1)
    rw [heq]
    exact ⟨Cover.ofDesign hH⟩
  have hpred := modular_predecessor (by omega : 2≤m) hFm
  let D := restrict hpred.some (by decide : 30≤39)
  have hm' : Local (m-1+1) := by simpa only [Nat.sub_add_cancel (by omega : 1≤m)] using seed
  have hT := grow (r := 29) (a := 1) D local_thirty local_thirty_one (by omega) (by decide)
    hm' local_thirty
  have hT' := grow (r := 30) (a := 1) D local_thirty local_thirty_one (by omega) (by decide)
    hm' local_thirty_one
  have hmT : P ∣ 30*m := hPm.trans (dvd_mul_left ..)
  refine ⟨30*m,by omega,⟨?_,large_factors (by omega) hmT⟩,⟨?_,?_⟩⟩
  · convert hT using 1
    omega
  · convert hT' using 1
    omega
  · refine ⟨modular (by omega) ?_⟩
    apply Nat.Coprime.of_dvd_left (hF.trans hmT)
    simp

#print axioms grow
#print axioms adjacent_heights
end Erdos722.Six
