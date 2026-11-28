import Erdos478EffectiveSplitting

/-!
# The size of the splitting-prime bound for factorial gaps

Keep the factorial degree as a separate parameter. The logarithm of the
prime bound is at most cubic in this parameter, up to a polynomial in the
gap length.
-/

namespace Erdos478.EffectiveResolvent

theorem add_bound {a b i j : ℕ} (ha : a ≤ 2^i) (hb : b ≤ 2^j) :
    a+b ≤ 2^(i+j+1) := by
  rw [pow_succ,Nat.mul_two]
  exact Nat.add_le_add (ha.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    (hb.trans (Nat.pow_le_pow_right (by decide) (by omega)))

theorem mul_bound {a b i j : ℕ} (ha : a ≤ 2^i) (hb : b ≤ 2^j) :
    a*b ≤ 2^(i+j) := by rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem pow_bound {a i n m : ℕ} (ha : a ≤ 2^i) (hn : n≤m) :
    a^n ≤ 2^(i*m) := by
  rw [pow_mul]
  exact (Nat.pow_le_pow_left ha _).trans (Nat.pow_le_pow_right (by positivity) hn)

private theorem exponent_bound (b m : ℕ) (hb : 4 ≤ b) (hm : 1 ≤ m) :
    let H := b+b+(b+b^2*2+0+1)*b
    let E := (1+b)*(b*b)+(1+H)*(m*m)
    ((1+H+1+1)+((1+H+0+1)+E+(1+H+1+1)*m*2)+1)*m ≤ b^8*m^3 := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hm
  dsimp
  ring_nf
  omega

theorem splitBound_gap_le (n : ℕ) (hn : 2≤n) :
    splitBound n (n+1) ≤ 2^((n+2)^(3*n+8)) := by
  let b := n+2
  let m := b^n
  have hn' : n≤b := by dsimp [b]; omega
  have hb : b≤2^b := Nat.lt_two_pow_self.le
  have Hn : n ≤ 2^b := hn'.trans hb
  have Hu : n+1 ≤ 2^b := (show n+1 ≤ b by dsimp [b]; omega).trans hb
  have Hm : n.factorial ≤ m := (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hn' _)
  have Hm' : n.factorial ≤ 2^(b^2) := by
    apply Hm.trans
    simpa only [pow_two] using pow_bound hb hn'
  have one : 1 ≤ (2:ℕ)^0 := by decide
  have two : 2 ≤ (2:ℕ)^1 := by decide
  let H := b+b+(b+b^2*2+0+1)*b
  have hs := mul_bound (mul_bound Hn Hu) (pow_bound (add_bound (mul_bound Hn (pow_bound Hm' (le_refl 2))) one) hn')
  have hH : tagBound n (n+1) ≤ 2^H := hs
  let E := (1+b)*(b*b)+(1+H)*(m*m)
  have hE : exceptionalBound n (n+1) ≤ 2^E :=
    mul_bound (pow_bound (mul_bound two Hu) (by simpa [pow_two] using Nat.mul_le_mul hn' hn'))
      (pow_bound (mul_bound two hH) (by simpa [pow_two] using Nat.mul_le_mul Hm Hm))
  have h₁ := add_bound (mul_bound two hH) one
  have h₂ := add_bound (mul_bound two hH) two
  have he := pow_bound (add_bound h₂ (mul_bound (mul_bound h₁ hE)
    (pow_bound (pow_bound h₂ Hm) (le_refl 2)))) Hm
  apply he.trans
  apply Nat.pow_le_pow_right (by decide)
  calc
    _ ≤ b^8*m^3 := exponent_bound b m (by dsimp [b]; omega) (by dsimp [m,b]; exact Nat.one_le_pow _ _ (by omega))
    _ = _ := by dsimp [b,m]; rw [← pow_mul,← pow_add]; congr 1; omega

#print axioms splitBound_gap_le
end Erdos478.EffectiveResolvent
