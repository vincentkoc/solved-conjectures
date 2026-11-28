import Erdos722AffineIngredients
import Erdos722CyclotomicSpectrum

/-!
# Adjacent usable widths for arbitrary block size

A sufficiently large prime congruent to one modulo a chosen multiple of
k(k−1) supplies both adjacent counts. The first uses a shared point, and
the second fills each of the k columns separately.
-/

namespace Erdos722.PairDesign
open Finset Erdos722.Quartet

theorem adjacent_multiples {k : ℕ} (hk : 2≤k) (M B : ℕ) (hM : 0<M) :
    ∃ s ≥ B, k ∣ s ∧ M ∣ s ∧ Adjacent k s := by
  obtain ⟨N,arr⟩ := eventual_arrays hk
  let P := k*M*(k-1)
  have hP : 0<P := Nat.mul_pos (Nat.mul_pos (by omega) hM) (by omega)
  obtain ⟨q,hq,hqN,hm⟩ := Nat.exists_prime_gt_modEq_one (max B (max N (Cyclotomy.cutoff k))) hP.ne'
  obtain ⟨a,ha⟩ := (Nat.modEq_iff_dvd' hq.one_le).mp hm.symm
  let m := k*M*a
  let t := (k-1)*m
  have he : t=q-1 := by rw [ha]; dsimp [t,m,P]; ring
  have htq : t+1=q := by omega
  have htN : N≤t := by omega
  have hts : t≤k*m := Nat.mul_le_mul_right m (Nat.sub_le ..)
  have hpdiv : k*(k-1) ∣ q-1 := ⟨M*a,by rw [ha]; dsimp [P]; ring⟩
  obtain ⟨H,hH⟩ := Cyclotomy.prime_power_design hq.isPrimePow hk (by omega) hpdiv
  have D : Has (·=k) (t+1) := htq ▸ ⟨Cover.ofDesign hH⟩
  have h₀ := array_fill (by omega : 0<k) (arr t htN) (S:=(· = k)) rfl (a:=1) le_rfl D
  have h₁ := array_fill (by omega : 0<k) (arr (t+1) (by omega)) (S:=(· = k)) rfl (a:=0) (by decide) D
  have hpred : k-1+1=k := by omega
  refine ⟨k*m,by omega,dvd_mul_right ..,⟨k*k*a,by dsimp [m]; ring⟩,?_,?_⟩
  · change Has (·=k) ((k-1)*(k*m)+1)
    rw [show (k-1)*(k*m)+1=k*t+1 by dsimp [t]; ring]
    exact h₀
  · change Has (·=k) ((k-1)*(k*m+1)+1)
    rw [show (k-1)*(k*m+1)+1=k*(t+1)+0 by dsimp [t]; nlinarith only [hpred]]
    exact h₁

theorem unrestricted_heights {k : ℕ} (hk : 2≤k) (s B : ℕ) (hs : 0<s) :
    ∃ t ≥ B, Adjacent k t ∧ ArrayAt (s+1) t ∧ ArrayAt (s+1) (t+1) := by
  obtain ⟨N,arr⟩ := eventual_arrays (by omega : 2 ≤ s+1)
  obtain ⟨t,ht,_,_,h⟩ := adjacent_multiples hk 1 (max B N) (by decide)
  exact ⟨t,by omega,h,arr _ (by omega),arr _ (by omega)⟩

#print axioms adjacent_multiples
#print axioms unrestricted_heights
end Erdos722.PairDesign
