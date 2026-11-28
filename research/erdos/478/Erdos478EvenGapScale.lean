import Erdos478EvenGapFamily
import Erdos478ResolventScale

/-!
# An explicit bound for simultaneous even-gap witnesses

Keep the factorial degree as a separate parameter. The logarithm of the
prime bound is at most cubic in this parameter, up to a polynomial in the
gap length.
-/

namespace Erdos478.EffectiveResolvent

private theorem exponent_bound (b m : ℕ) (hb : 4 ≤ b) (hm : 1 ≤ m) :
    let H := b+b+(b+b^2*2+0+1)*b
    let E := 1+(1+b)*((b*b)*(b*b))+(1+H)*(m*m)
    ((1+H+1+1)+((1+H+0+1)+E+(1+H+1+1)*m*2)+1)*m ≤ b^9*m^3 := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hm
  dsimp
  ring_nf
  omega

theorem evenWitnessBound_le (n : ℕ) (hn : 0<n) :
    evenWitnessBound n ≤ 2^((2*n+4)^(3*n+9)) := by
  let b := 2*n+4
  let m := b^n
  have hn' : n≤b := by dsimp [b]; omega
  have hb : b≤2^b := Nat.lt_two_pow_self.le
  have Hn : n ≤ 2^b := hn'.trans hb
  have Hu : 2*n+1 ≤ 2^b := (show 2*n+1 ≤ b by dsimp [b]; omega).trans hb
  have Hm : evenWordDegree n ≤ m := by
    change (∏ i : Fin n, 2*(i.val+1)) ≤ b^n
    calc _ ≤ ∏ _i : Fin n, b := Finset.prod_le_prod' (fun i _ => by dsimp [b]; omega)
         _ = _ := by simp
  have Hm' : evenWordDegree n ≤ 2^(b^2) := by
    apply Hm.trans
    simpa only [pow_two] using pow_bound hb hn'
  have one : 1 ≤ (2:ℕ)^0 := by decide
  have two : 2 ≤ (2:ℕ)^1 := by decide
  let H := b+b+(b+b^2*2+0+1)*b
  have hs := mul_bound (mul_bound Hn Hu) (pow_bound (add_bound (mul_bound Hn (pow_bound Hm' (le_refl 2))) one) hn')
  have hH : wordBound n (evenWordDegree n) (2*n+1) ≤ 2^H := hs
  let E := 1+(1+b)*((b*b)*(b*b))+(1+H)*(m*m)
  have hN : n*(2*n) ≤ b*b := Nat.mul_le_mul hn' (by dsimp [b]; omega)
  have hE : 2*(2*(2*n+1))^((n*(2*n))^2)*(2*wordBound n (evenWordDegree n) (2*n+1))^((evenWordDegree n)^2) ≤ 2^E :=
    mul_bound (mul_bound two (pow_bound (mul_bound two Hu) (by simpa [pow_two] using Nat.mul_le_mul hN hN)))
      (pow_bound (mul_bound two hH) (by simpa [pow_two] using Nat.mul_le_mul Hm Hm))
  have h₁ := add_bound (mul_bound two hH) one
  have h₂ := add_bound (mul_bound two hH) two
  have he := pow_bound (add_bound h₂ (mul_bound (mul_bound h₁ hE)
    (pow_bound (pow_bound h₂ Hm) (le_refl 2)))) Hm
  apply he.trans
  apply Nat.pow_le_pow_right (by decide)
  calc
    _ ≤ b^9*m^3 := exponent_bound b m (by dsimp [b]; omega) (by dsimp [m,b]; exact Nat.one_le_pow _ _ (by omega))
    _ = _ := by dsimp [b,m]; rw [← pow_mul,← pow_add]; congr 1; omega

#print axioms evenWitnessBound_le
end Erdos478.EffectiveResolvent
