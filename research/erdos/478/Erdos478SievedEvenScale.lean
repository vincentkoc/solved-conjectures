import Erdos478SievedSchurPrime
import Erdos478EvenGapScale

/-!
# A quadratic degree estimate for the even-gap prime

Sieving the exceptional primes removes a full factor of the common-root
resolvent degree from the logarithm of the prime ceiling.
-/

namespace Erdos478.EffectiveResolvent

private def heightExp (b : ℕ) := b+b+(b+b^2*2+0+1)*b
private def badExp (b m : ℕ) := 1+(1+b)*((b*b)*(b*b))+(1+heightExp b)*(m*m)

private theorem bit_budget {b m B D : ℕ} (hb : 4≤b) (hm : m ≤ 2^(b^2))
    (hd : D ≤ 2^(b^2)) (hB : B ≤ 2^(badExp b m)) : sieveBits D B ≤ b^6 := by
  apply Nat.clog_le_of_le_pow
  apply max_le
  · apply (add_bound hd (by decide : 1≤(2:ℕ)^0)).trans
    apply Nat.pow_le_pow_right (by decide)
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hb
    ring_nf
    omega
  · have hl := (Nat.log_mono_right (b := 2) hB).trans_eq (Nat.log_pow (by decide) _)
    have small : 1+(1+b)*((b*b)*(b*b)) ≤ 2^(1+(1+b)*((b*b)*(b*b))) := Nat.lt_two_pow_self.le
    have ht : 1+heightExp b ≤ 2^(1+heightExp b) := Nat.lt_two_pow_self.le
    have hE := add_bound small (mul_bound ht (mul_bound hm hm))
    apply (add_bound (hl.trans hE) (by decide : 1≤(2:ℕ)^0)).trans
    apply Nat.pow_le_pow_right (by decide)
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hb
    dsimp [heightExp]
    ring_nf
    omega

private theorem final_exponent (b m : ℕ) (hb : 4≤b) (hm : 1 ≤ m) :
    let H := heightExp b
    let S := b^2*m + 32*(m+1)*(b^6+1)^2
    ((1+H+1+1)+((1+H+0+1)+S+(1+H+1+1)*m*2)+1)*m ≤ b^17*m^2 := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hm
  dsimp [heightExp]
  ring_nf
  omega

theorem sieved_even_bound (n : ℕ) :
    evenBoundWith sievedSchur n ≤ 2^((2*n+4)^(2*n+17)) := by
  let b := 2*n+4
  let m := b^n
  let D := evenWordDegree n
  let V := wordBound n D (2*n+1)
  let B := 2*(2*(2*n+1))^((n*(2*n))^2)*(2*V)^(D^2)
  have hb : 4≤b := by dsimp [b]; omega
  have hm : m ≤ 2^(b^2) := by
    simpa only [pow_two] using pow_bound (Nat.lt_two_pow_self.le : b ≤ 2^b) (by dsimp [b]; omega : n≤b)
  obtain ⟨hD,hD',hH,hE⟩ := even_resolvent_sizes n
  have hbgt : sieveBits D B ≤ b^6 := bit_budget hb hm hD' hE
  have hfac : D.factorial ≤ 2^(b^2*m) := (Nat.factorial_le_pow D).trans (pow_bound hD' hD)
  have hsearch : 2^(32*(D+1)*(sieveBits D B+1)^2) ≤ 2^(32*(m+1)*(b^6+1)^2) := by
    gcongr
    decide
  have hS := mul_bound hfac hsearch
  have one : 1 ≤ (2:ℕ)^0 := by decide
  have two : 2 ≤ (2:ℕ)^1 := by decide
  have h₁ := add_bound (mul_bound two hH) one
  have h₂ := add_bound (mul_bound two hH) two
  have he := pow_bound (add_bound h₂ (mul_bound (mul_bound h₁ hS)
    (pow_bound (pow_bound h₂ hD) (le_refl 2)))) hD
  apply he.trans
  apply Nat.pow_le_pow_right (by decide)
  calc
    _ ≤ b^17*m^2 := final_exponent b m hb (Nat.one_le_pow _ _ (by omega))
    _ = _ := by dsimp [b,m]; rw [← pow_mul,← pow_add]; congr 1; omega

#print axioms sieved_even_bound

end Erdos478.EffectiveResolvent
