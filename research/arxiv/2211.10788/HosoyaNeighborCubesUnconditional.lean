import HosoyaProductCubeDescent
import HosoyaNeighborProductPowers

/-! Unconditional exclusion of cubes for the product of the neighboring Hosoya entries. -/

namespace Arxiv.«2211.10788»

private theorem fib_cycle (n : ℕ) : Nat.fib n ≡ Nat.fib (n%48) [MOD 252] := by
  have shift (i : ℕ) : Nat.fib (i+48) ≡ Nat.fib i [MOD 252] := by
    induction i using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more i h₀ h₁ =>
      rw [show i+2+48=i+48+2 by omega,Nat.fib_add_two (n:=i+48),Nat.fib_add_two (n:=i)]
      exact h₀.add h₁
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<48
    · rw [Nat.mod_eq_of_lt hn]
    · let i := n-48
      have he : n=i+48 := by dsimp [i]; omega
      have hi : i<n := by omega
      rw [he,Nat.add_mod_right]
      exact (shift i).trans (ih i hi)

private theorem cube_forces_eighteen {n y : ℕ} (he : y^3+1=11*(Nat.fib n)^2) :
    18 ∣ Nat.fib n := by
  have table : ∀ i : Fin 48, 18 ∣ Nat.fib i ∨
      (∀ z : Fin 28, ¬ z.val^3+1 ≡ 11*(Nat.fib i)^2 [MOD 28]) ∨
      (∀ z : Fin 9, ¬ z.val^3+1 ≡ 11*(Nat.fib i)^2 [MOD 9]) := by decide
  have red := fib_cycle n
  have residue {d : ℕ} (hd : d ∣ 252) :
      (y%d)^3+1 ≡ 11*(Nat.fib (n%48))^2 [MOD d] := by
    apply (((Nat.mod_modEq y d).pow 3).add_right 1).trans
    rw [he]; exact ((red.of_dvd hd).pow 2).mul_left 11
  rcases table ⟨n%48,Nat.mod_lt _ (by decide)⟩ with h|h|h
  · exact Nat.modEq_zero_iff_dvd.mp ((red.of_dvd (by decide : 18 ∣ 252)).trans (Nat.modEq_zero_iff_dvd.mpr h))
  · exact False.elim (h ⟨y%28,Nat.mod_lt _ (by decide)⟩ (residue (by decide)))
  · exact False.elim (h ⟨y%9,Nat.mod_lt _ (by decide)⟩ (residue (by decide)))

/-- For every index, 11 times the squared Fibonacci number cannot be one more
than a nonnegative cube. -/
theorem fib_cube_add_one_ne_eleven_square (n y : ℕ) : y^3+1≠11*(Nat.fib n)^2 := by
  intro he
  have hd := cube_forces_eighteen he
  have hz := (HosoyaCubeNorm.cube_norm_at_eighteen (Nat.fib n) y (by exact_mod_cast hd)
    (by exact_mod_cast he)).2
  omega

/-- No product of the two neighboring diagonal entries is a cube. The
index in this statement is the physical index m+2. -/
theorem neighboring_product_ne_cube_unconditional (m y : ℕ) :
    lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^3 := by
  intro he
  rcases Nat.even_or_odd m with hm | hm
  · have hz := lucasFibonacciSum_mul_lowerNeighbor m
    have hi : (lucasFibonacciSum (m+2) : ℤ)*lowerNeighborAtAddTwo m=(y:ℤ)^3 := by exact_mod_cast he
    rw [hi,hm.neg_one_pow] at hz
    have norm : (y:ℤ)^3+1=11*(Nat.fib (m+2):ℤ)^2 := by omega
    exact fib_cube_add_one_ne_eleven_square (m+2) y (by exact_mod_cast norm)
  · have hh := odd_neighbor_product_mod_seven m hm
    have hv := congrArg (Nat.castRingHom (ZMod 7)) he
    simp only [map_mul,map_pow,Nat.coe_castRingHom] at hv
    rw [hv] at hh
    exact (by decide : ∀ t : ZMod 7, ¬(t^3=3 ∨ t^3=5)) _ hh

/-- The Bennett–Skinner coefficient-eleven statement alone suffices to rule
out every proper power for the neighboring product. -/
theorem neighboring_product_ne_power_of_fermat_eleven (fermat : BennettSkinnerEleven)
    (m y k : ℕ) (hk : 2 ≤ k) : lucasFibonacciSum (m+2)*lowerNeighborAtAddTwo m ≠ y^k :=
  neighboring_product_ne_power_of_cube_exclusion fermat m y k hk (neighboring_product_ne_cube_unconditional m y)

#print axioms neighboring_product_ne_power_of_fermat_eleven
#print axioms fib_cube_add_one_ne_eleven_square
#print axioms neighboring_product_ne_cube_unconditional

end Arxiv.«2211.10788»
