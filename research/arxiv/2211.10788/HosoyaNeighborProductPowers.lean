import NeighboringLucasFibonacciPrimes

/-! Perfect powers in the product of the two neighboring Hosoya entries. -/

namespace Arxiv.«2211.10788»

private theorem fib_mod_seven_period (i : ℕ) :
    Nat.fib (i+16) ≡ Nat.fib i [MOD 7] := by
  induction i using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more i h₀ h₁ =>
    rw [show i+2+16=i+16+2 by omega, Nat.fib_add_two (n:=i+16), Nat.fib_add_two (n:=i)]
    exact h₀.add h₁

private theorem fib_seven_reduce (i : ℕ) :
    (Nat.fib i : ZMod 7) = Nat.fib (i%16) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < 16
    · rw [Nat.mod_eq_of_lt hi]
    · let j := i-16
      have he : i=j+16 := by dsimp [j]; omega
      have hl : j < i := by omega
      have hf := (ZMod.natCast_eq_natCast_iff ..).mpr (fib_mod_seven_period j)
      rw [he, hf]
      simpa only [Nat.add_mod_right] using ih j hl

/-- At positive odd indices the product is 3 or 5 modulo 7. -/
theorem odd_neighbor_product_mod_seven (m : ℕ) (hm : Odd m) :
    let a : ZMod 7 := (lucasFibonacciSum (m+2) : ZMod 7) * lowerNeighborAtAddTwo m
    a=3 ∨ a=5 := by
  have hz := congrArg (Int.castRingHom (ZMod 7)) (lucasFibonacciSum_mul_lowerNeighbor m)
  simp only [hm.neg_one_pow, map_mul, map_sub, map_pow, map_neg, map_one, map_ofNat,
    Int.coe_castRingHom, Int.cast_natCast] at hz
  dsimp only
  rw [hz, fib_seven_reduce]
  have ht : (m+2)%16<16 := Nat.mod_lt _ (by decide)
  have hodd : (m+2)%16%2=1 := by obtain ⟨u,hu⟩ := hm; omega
  generalize (m+2)%16 = i at *
  interval_cases i <;> first | omega | decide

/-- The product is never square, at either parity of the physical index m+2. -/
theorem neighboring_product_ne_square (m y : ℕ) :
    lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^2 := by
  intro he
  rcases Nat.even_or_odd m with hm | hm
  · have hz := lucasFibonacciSum_mul_lowerNeighbor m
    have hi : (lucasFibonacciSum (m+2) : ℤ)*lowerNeighborAtAddTwo m=(y:ℤ)^2 := by exact_mod_cast he
    rw [hi, hm.neg_one_pow] at hz
    have hv := congrArg (Int.castRingHom (ZMod 11)) hz
    simp only [map_pow,map_sub,map_mul,map_one,map_ofNat,Int.coe_castRingHom,Int.cast_natCast] at hv
    exact (by decide : ∀ t u : ZMod 11, t^2 ≠ 11*u^2-1) _ _ hv
  · have hh := odd_neighbor_product_mod_seven m hm
    have hev : (lucasFibonacciSum (m+2) : ZMod 7)*lowerNeighborAtAddTwo m=(y:ZMod 7)^2 := by exact_mod_cast (congrArg (Nat.castRingHom (ZMod 7)) he)
    rw [show (lucasFibonacciSum (m+2) : ZMod 7)*lowerNeighborAtAddTwo m=(y:ZMod 7)^2 from hev] at hh
    exact (by decide : ∀ t : ZMod 7, ¬(t^2=3 ∨ t^2=5)) _ hh

#print axioms odd_neighbor_product_mod_seven
#print axioms neighboring_product_ne_square


/-- The C=11 case of Bennett and Skinner, Theorem 1.1, in the order x>y. -/
def BennettSkinnerEleven : Prop :=
  ∀ (k : ℕ) (x y z : ℤ), 4 ≤ k → y < x → x ≠ 0 → y ≠ 0 → z ≠ 0 →
    IsCoprime x y → IsCoprime x z → IsCoprime y z →
    x^k+y^k=11*z^2 → k=5 ∧ x=3 ∧ y=2 ∧ z.natAbs=5

/-- The X-coordinates of the k=1331 row in Bennett and Ghadermarzi. -/
def Mordell1331RowComplete : Prop :=
  ∀ X Y : ℤ, Y^2=X^3+1331 → X = -11 ∨ X=37

private theorem neighbor_product_gt_one (m : ℕ) :
    1 < lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m := by
  have hp : 0 < Nat.fib (m+2) := Nat.fib_pos.mpr (by omega)
  unfold lucasFibonacciSum lowerNeighborAtAddTwo
  nlinarith

theorem neighboring_product_ne_cube (row : Mordell1331RowComplete) (m y : ℕ) :
    lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^3 := by
  intro he
  rcases Nat.even_or_odd m with hm | hm
  · have hz := lucasFibonacciSum_mul_lowerNeighbor m
    have hi : (lucasFibonacciSum (m+2) : ℤ)*lowerNeighborAtAddTwo m=(y:ℤ)^3 := by exact_mod_cast he
    rw [hi, hm.neg_one_pow] at hz
    have hrow := row (11*y) (121*Nat.fib (m+2)) (by linear_combination -1331*hz)
    omega
  · have hh := odd_neighbor_product_mod_seven m hm
    have hev : (lucasFibonacciSum (m+2) : ZMod 7)*lowerNeighborAtAddTwo m=(y:ZMod 7)^3 := by
      exact_mod_cast (congrArg (Nat.castRingHom (ZMod 7)) he)
    rw [hev] at hh
    exact (by decide : ∀ t : ZMod 7, ¬(t^3=3 ∨ t^3=5)) _ hh

/-- The coefficient-eleven Fermat input leaves only the cubic case after square exclusion. -/
theorem neighboring_product_ne_power_of_cube_exclusion (fermat : BennettSkinnerEleven)
    (m y k : ℕ) (hk : 2 ≤ k)
    (cube : lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^3) :
    lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^k := by
  intro he
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨r,hr⟩ := heven
    exact neighboring_product_ne_square m (y^r) (by rwa [← pow_mul, show r*2=k by omega])
  by_cases h3 : k=3
  · subst k
    exact cube he
  have hk4 : 4 ≤ k := by obtain ⟨r,hr⟩ := hodd; omega
  have hbig := neighbor_product_gt_one m
  rw [he] at hbig
  have hy : 1 < y := by
    by_contra! hn
    interval_cases y <;> simp [show k≠0 by omega] at hbig
  let f : ℕ := Nat.fib (m+2)
  have hf : 0 < f := Nat.fib_pos.mpr (by omega)
  have hz := lucasFibonacciSum_mul_lowerNeighbor m
  have hi : (lucasFibonacciSum (m+2) : ℤ)*lowerNeighborAtAddTwo m=(y:ℤ)^k := by exact_mod_cast he
  rw [hi] at hz
  change (y:ℤ)^k=11*(f:ℤ)^2-(-1)^m at hz
  have hcp : IsCoprime (y:ℤ) (f:ℤ) := by
    apply IsCoprime.of_isCoprime_of_dvd_left (y := (y:ℤ)^k) _ (dvd_pow_self _ (by omega))
    rw [hz]
    have hs : (-1:ℤ)^m * (-1)^m = 1 := by
      rw [← mul_pow]; simp
    exact ⟨-((-1)^m),11*(f:ℤ)*(-1)^m,by linear_combination hs⟩
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow] at hz
    have h := fermat k y 1 f hk4 (by omega) (by omega) (by decide) (by omega)
      isCoprime_one_right hcp isCoprime_one_left (by simpa using (show (y:ℤ)^k+1=11*(f:ℤ)^2 by omega))
    omega
  · rw [hm.neg_one_pow] at hz
    have h := fermat k y (-1) f hk4 (by omega) (by omega) (by decide) (by omega)
      isCoprime_one_right.neg_right hcp isCoprime_one_left.neg_left (by rw [hodd.neg_one_pow]; omega)
    omega

/-- At every physical index at least two the product of the neighboring
entries is free of proper powers, from the stated published classifications. -/
theorem neighboring_product_ne_power (fermat : BennettSkinnerEleven) (row : Mordell1331RowComplete)
    (m y k : ℕ) (hk : 2 ≤ k) :
    lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^k :=
  neighboring_product_ne_power_of_cube_exclusion fermat m y k hk (neighboring_product_ne_cube row m y)

#print axioms neighboring_product_ne_power_of_cube_exclusion
#print axioms neighboring_product_ne_cube
#print axioms neighboring_product_ne_power

end Arxiv.«2211.10788»
