import Erdos478SievedEvenScale
import Erdos478ExclusionBits
import Erdos478AvoidanceCount

/-!
# Explicit multiplicity of simultaneous factorial-gap witnesses

For every positive number of even gaps and every bit count `L`, one
explicit interval contains more than `2^L` distinct witness primes.
-/

namespace Erdos478.EffectiveResolvent
open Finset

def witnessCeiling (n L : ℕ) :=
  let b := 2*n+4
  2^(b^19*(b^n)^2*(L+1)^2)

private theorem scaled_exponent (b m L : ℕ) (hb : 4≤b) (hm : 1 ≤ m) :
    schurExponent b m (b^7*(L+1)) ≤ b^19*m^2*(L+1)^2 := by
  have scale (K w : ℕ) (hw : 1≤w) :
      schurExponent b m (K*w) ≤ schurExponent b m K * w^2 := by
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hw
    dsimp [schurExponent]
    generalize heightExp b = H
    ring_nf
    omega
  calc
    _ = schurExponent b m (b^6*(b*(L+1))) := by rw [pow_succ b 6,Nat.mul_assoc]
    _ ≤ _ := scale _ _ (Nat.mul_pos (by omega) (by omega))
    _ ≤ (b^17*m^2)*(b*(L+1))^2 :=
      Nat.mul_le_mul_right _ (base_exponent_bound b m hb hm)
    _ = _ := by ring

theorem avoiding_ceiling (n L C : ℕ) (hC : C ≤ (witnessCeiling n L)^(2^L)) :
    evenBoundAvoidingWith sievedSchur n C ≤ witnessCeiling n L := by
  let b := 2*n+4
  let m := b^n
  let D := evenWordDegree n
  let V := wordBound n D (2*n+1)
  let B := 2*(2*(2*n+1))^((n*(2*n))^2)*(2*V)^(D^2)
  have hb : 4≤b := by dsimp [b]; omega
  have hm : m ≤ 2^(b^2) := by
    simpa only [pow_two] using pow_bound (Nat.lt_two_pow_self.le : b ≤ 2^b) (by dsimp [b]; omega : n≤b)
  obtain ⟨hD,hD',hH,hE⟩ := even_resolvent_sizes n
  have hbase : sieveBits D B ≤ b^6 := bit_budget hb hm hD' hE
  let l := b*19 + b^2*2 + (L+1)*2 + L
  have hM := mul_bound (mul_bound (pow_bound (Nat.lt_two_pow_self.le : b≤2^b) (le_refl 19))
    (pow_bound hm (le_refl 2))) (pow_bound (Nat.lt_two_pow_self.le : L+1≤2^(L+1)) (le_refl 2))
  have hC' : C ≤ 2^(2^l) := by
    change C ≤ (2^(b^19*m^2*(L+1)^2))^(2^L) at hC
    rw [← pow_mul] at hC
    exact hC.trans (Nat.pow_le_pow_right (by decide) (mul_bound hM (le_refl (2^L))))
  have hbits : sieveBits D (C*B) ≤ b^7*(L+1) := by
    apply (sieveBits_extra hbase hC').trans
    dsimp [l]
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hb
    rw [hv]
    ring_nf
    omega
  exact (schur_bound_of_bits hD hD' hH hbits).trans (Nat.pow_le_pow_right (by decide)
    (scaled_exponent b m L hb (Nat.one_le_pow _ _ (by omega))))

open scoped Classical in
/-- Each prime counted here has two distinct collision endpoints at every even
length through `2*n`, with the endpoints disjoint across lengths. -/
theorem many_even_witnesses (n L : ℕ) (hn : 0<n) :
    2^L < ((range (witnessCeiling n L+1)).filter (EvenGapWitness n)).card := by
  apply count_of_avoidance (by unfold witnessCeiling; positivity) _ (fun _ h => h.1.pos)
  intro C hC hbound
  obtain ⟨p,hp,havoid,hw⟩ := simultaneous_even_avoiding sievedSchur n C hn hC
  exact ⟨p,hp.trans (avoiding_ceiling n L C hbound),hw,havoid⟩

#print axioms avoiding_ceiling
#print axioms many_even_witnesses

end Erdos478.EffectiveResolvent
