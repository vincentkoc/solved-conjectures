import HosoyaLucasWindowBounds

/-! Odd parts of Lucas numbers along a dyadic sequence of even indices. -/

namespace Arxiv.«2211.10788».ProgressionClosure

lemma lucas_double {h : ℕ} (he : Even h) : lucas (2*h)+2 = (lucas h)^2 := by
  have hn := fib_pair_norm h
  rw [he.neg_one_pow] at hn
  have hd := Int.fib_two_mul (h:ℤ)
  have ho := Int.fib_two_mul_add_one (h:ℤ)
  have a : (Nat.fib (2*h):ℤ) = Nat.fib h*(2*(Nat.fib (h+1):ℤ)-Nat.fib h) := by
    simpa only [show (2:ℤ)*h=((2*h:ℕ):ℤ) by push_cast; ring,
      show (h:ℤ)+1=((h+1:ℕ):ℤ) by push_cast; rfl,Int.fib_natCast] using hd
  have b : (Nat.fib (2*h+1):ℤ) = (Nat.fib (h+1):ℤ)^2+(Nat.fib h:ℤ)^2 := by
    simpa only [show (2:ℤ)*h+1=((2*h+1:ℕ):ℤ) by push_cast; ring,
      show (h:ℤ)+1=((h+1:ℕ):ℤ) by push_cast; rfl,Int.fib_natCast] using ho
  have e : (lucas (2*h):ℤ)+2 = (lucas h:ℤ)^2 := by
    rw [lucas_cast,lucas_cast,a,b]
    linear_combination -2*hn
  exact_mod_cast e

/-- Every radius is an even multiple of the original progression window. -/
def radius (d : ℕ) (y : ℤ) (k : ℕ) : ℕ := 2^k*(2*window d y)

lemma radius_succ (d : ℕ) (y : ℤ) (k : ℕ) :
    radius d y (k+1) = 2*radius d y k := by simp [radius,pow_succ]; ring

lemma radius_even (d : ℕ) (y : ℤ) (k : ℕ) : Even (radius d y k) :=
  ⟨2^k*window d y,by dsimp [radius]; ring⟩

lemma radius_pos {d : ℕ} (hd : 0 < d) (y : ℤ) (k : ℕ) : 0 < radius d y k := by
  dsimp [radius,window]; positivity

lemma step_dvd_radius (d : ℕ) (y : ℤ) (k : ℕ) : d ∣ radius d y k :=
  ⟨2^k*4*((threshold y).log2+1),by dsimp [radius,window]; ring⟩

/-- The full Lucas number with at most one factor of two removed. -/
def oddLucas (h : ℕ) : ℕ := if 2 ∣ lucas h then lucas h/2 else lucas h

lemma oddLucas_dvd (h : ℕ) : oddLucas h ∣ lucas h := by
  unfold oddLucas
  split_ifs with he
  · exact ⟨2,by omega⟩
  · rfl

lemma lucas_le_twice_odd (h : ℕ) : lucas h ≤ 2*oddLucas h := by
  unfold oddLucas
  split_ifs <;> omega

private lemma double_not_four {h : ℕ} (he : Even h) : ¬4 ∣ lucas (2*h) := by
  have e := lucas_double he
  have sq : (lucas h)^2%4 = 0 ∨ (lucas h)^2%4 = 1 := by
    rw [Nat.pow_mod]; have := Nat.mod_lt (lucas h) (by decide : 0<4)
    interval_cases lucas h % 4 <;> decide
  omega

theorem odd_layer (d : ℕ) (y : ℤ) (k : ℕ) : ¬2 ∣ oddLucas (radius d y k) := by
  have hn : ¬4 ∣ lucas (radius d y k) := by
    cases k with
    | zero =>
      simpa [radius] using double_not_four (show Even (window d y) from even_two_mul _)
    | succ k => rw [radius_succ]; exact double_not_four (radius_even d y k)
  unfold oddLucas
  split_ifs <;> omega

theorem layer_size {d : ℕ} (hd : 0 < d) (y : ℤ) (k : ℕ) :
    threshold y < oddLucas (radius d y k) := by
  have big : 2*threshold y < lucas (radius d y k) := by
    have hs : 3 ≤ threshold y := by unfold threshold; omega
    induction k with
    | zero =>
      have e := lucas_double (show Even (window d y) from even_two_mul _)
      have h := window_size hd y
      simp only [radius,pow_zero,one_mul]
      nlinarith [Nat.mul_self_le_mul_self (show threshold y+1 ≤ lucas (window d y) by omega)]
    | succ k ih =>
      rw [radius_succ]
      have e := lucas_double (radius_even d y k)
      nlinarith [Nat.mul_self_le_mul_self (show 2*threshold y+1 ≤ lucas (radius d y k) by omega)]
  have := lucas_le_twice_odd (radius d y k)
  omega

#print axioms lucas_double
#print axioms odd_layer
#print axioms layer_size

end Arxiv.«2211.10788».ProgressionClosure
