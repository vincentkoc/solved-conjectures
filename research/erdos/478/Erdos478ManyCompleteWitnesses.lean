import Erdos478CompleteEvenCeiling
import Erdos478ExclusionBits
import Erdos478AvoidanceCount

/-!
# Counting primes with complete splitting of even factorial gaps

An excluded product of primes increases the bit parameter in the Schur
sieve. The resulting ceiling retains the triangular count of reflection
pairs from the complete splitting construction.
-/

namespace Erdos478.EffectiveResolvent
open Finset

def completeCeiling (n L : ℕ) := 2^((2*n+4)^(n*(n+1)+38)*(L+1)^2)

private theorem exclusion_exponent (A m L : ℕ) (hA : 4 ≤ A) (hm : 1 ≤ m) :
    schurExponent A m (A^7*(L+1)) ≤ A^19*m^2*(L+1)^2 := by
  have hscale (K w : ℕ) (hw : 1 ≤ w) :
      schurExponent A m (K*w) ≤ schurExponent A m K * w^2 := by
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hw
    dsimp [schurExponent]
    generalize heightExp A = H
    ring_nf
    omega
  calc
    _ = schurExponent A m (A^6*(A*(L+1))) := by rw [pow_succ A 6,Nat.mul_assoc]
    _ ≤ _ := hscale _ _ (Nat.mul_pos (by omega) (by omega))
    _ ≤ (A^17*m^2)*(A*(L+1))^2 :=
      Nat.mul_le_mul_right _ (base_exponent_bound A m hA hm)
    _ = _ := by ring

private theorem ceiling_form (n L : ℕ) :
    completeCeiling n L =
      2^(((2*n+4)^2)^19*((2*n+4)^pairCount n)^2*(L+1)^2) := by
  unfold completeCeiling
  rw [← pow_mul,← pow_mul,← pow_add,← twice_pairCount n]
  congr 3
  omega

theorem complete_avoiding {n L C : ℕ} (hn : 0<n) (hC : 0<C)
    (hbound : C ≤ (completeCeiling n L)^(2^L)) :
    ∃ p ≤ completeCeiling n L, CompleteEvenWitness n p ∧ ¬p∣C := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let r : Fin n ↪ ℕ := ⟨fun i => i.val+1,fun i j h => Fin.ext (by dsimp at h; omega)⟩
  have hr (i : Fin n) : 0<r i := Nat.succ_pos _
  have hu (i : Fin n) : 2*r i+1 ≤ 2*n+1 := by change 2*(i.val+1)+1 ≤ 2*n+1; omega
  obtain ⟨e,he,p,hp,hprime,havoid,hs,hd,hc⟩ :=
    effective_even_complete r hr (2*n+1) C hu hC sievedSchur
  let b := 2*n+4
  let A := b^2
  let N := pairCount n
  let m := b^N
  let D := pairedDegrees n
  let U := 2*n+1
  let V := wordBound N D U
  let B := (2*U)^((2*N)^2)*(2*V)^(D^2)
  change e ≤ D at he
  rw [Nat.mul_assoc] at hp
  change p ≤ sievedSchurBound e V (C*B) at hp
  change _+2*pairCount n ≤ p-1 at hc
  rw [twice_pairCount] at hc
  have hA : 4 ≤ A := by dsimp [A,b]; ring_nf; omega
  have hmpos : 1 ≤ m := Nat.one_le_pow _ _ (by dsimp [b]; omega)
  obtain ⟨hD,hm,hV,hB⟩ := paired_sizes n
  have hbase := bit_budget hA hm ((he.trans hD).trans hm) hB
  let l := A*19 + A^2*2 + (L+1)*2 + L
  have hi := mul_bound (mul_bound (pow_bound (Nat.lt_two_pow_self.le : A ≤ 2^A) (le_refl 19))
    (pow_bound hm (le_refl 2))) (pow_bound (Nat.lt_two_pow_self.le : L+1 ≤ 2^(L+1)) (le_refl 2))
  have hCl : C ≤ 2^(2^l) := by
    rw [ceiling_form,← pow_mul] at hbound
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (mul_bound hi (le_refl (2^L))))
  have hbits : sieveBits e (C*B) ≤ A^7*(L+1) := by
    apply (sieveBits_extra hbase hCl).trans
    dsimp [l]
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hA
    rw [hv]
    ring_nf
    omega
  refine ⟨p,hp.trans ?_,⟨hprime,hs,hd,hc⟩,havoid⟩
  rw [ceiling_form]
  exact (schur_bound_of_bits (he.trans hD) ((he.trans hD).trans hm) hV hbits).trans
    (Nat.pow_le_pow_right (by decide) (exclusion_exponent A m L hA hmpos))

open scoped Classical in
theorem many_complete_witnesses (n L : ℕ) (hn : 0<n) :
    2^L < ((range (completeCeiling n L+1)).filter (CompleteEvenWitness n)).card := by
  exact count_of_avoidance (by unfold completeCeiling; positivity) _ (fun _ h => h.1.pos)
    (fun _ hC hbound => complete_avoiding hn hC hbound)

#print axioms complete_avoiding
#print axioms many_complete_witnesses
end Erdos478.EffectiveResolvent
