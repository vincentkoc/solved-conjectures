import Erdos722IteratedSwitchCounts
import Erdos722QuadrupleSpectrum

/-!
# Quantitative families of canonical Steiner quadruple systems

For every admissible base order the exact exponent of the iterated construction
has a cubic expression. An arbitrary permutation of the final points is allowed
in the bound on genuinely nonisomorphic systems.
-/

namespace Erdos722.QuadSwitch
open Finset

theorem sharp_switch {V : Type*} [DecidableEq V] [Fintype V] {H : Finset (Finset V)}
    (hH : H.IsBlockDesign 3 4) (i : H) :
    ∃ D E : Finset (Finset (V × Bool)), D.IsBlockDesign 3 4 ∧ E.IsBlockDesign 3 4 ∧
      (D \ E).card = 8 ∧ (E \ D).card = 8 := by
  classical
  let f : H → Bool := fun _ => false
  let g : H → Bool := fun j => decide (j = i)
  refine ⟨doubling hH f,doubling hH g,doubling_design hH f,doubling_design hH g,?_,?_⟩
  · rw [distance]
    have one : (univ.filter fun j => f j ≠ g j) = {i} := by ext j; simp [f,g]
    simp [one]
  · rw [distance]
    have one : (univ.filter fun j => g j ≠ f j) = {i} := by ext j; simp [f,g]
    simp [one]

private theorem cubic_step (v : ℕ) (seed : Nonempty (Systems (Fin v))) :
    24*blockNumber v + 3*v^2 = v^3 + 2*v := by
  obtain ⟨H,hH⟩ := seed
  have hc := triple_incidence_count hH
  rw [base_block_count hH,Fintype.card_fin] at hc
  change blockNumber v * 4 = v.choose 3 at hc
  have hd := Nat.descFactorial_eq_factorial_mul_choose v 3
  change v.descFactorial 3 = 6 * v.choose 3 at hd
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,Nat.mul_one] at hd
  cases v with
  | zero => decide
  | succ v =>
    cases v with
    | zero => decide
    | succ v =>
      simp only [Nat.add_one_sub_one, show v+1+1-2 = v by omega] at hd
      nlinarith only [hc,hd]

theorem exponent_identity (v m : ℕ) (seed : Nonempty (Systems (Fin v))) :
    let n := 2^m*v
    168*switchExponent v m + v^3 + 7*n^2 + 14*v = n^3 + 7*v^2 + 14*n := by
  dsimp only
  induction m with
  | zero => simp [switchExponent]
  | succ m ih =>
    have pos : 0 < labelledCount v := Nat.card_pos_iff.mpr ⟨seed,inferInstance⟩
    have base : Nonempty (Systems (Fin (2^m*v))) := (Nat.card_pos_iff.mp
      ((Nat.mul_pos pos (pow_pos (by decide) _)).trans_le (iterate_count v m))).1
    have step := cubic_step _ base
    rw [show switchExponent v (m+1) = switchExponent v m + blockNumber (2^m*v) from sum_range_succ _ _,
      show 2^(m+1)*v = 2*(2^m*v) by rw [pow_succ]; ring]
    nlinarith only [ih,step]

/-- All Hanani-admissible seeds, with the vacuous small orders admitted by the host. -/
theorem admissible_orders (v m : ℕ) (hv : v ≤ 2 ∨ v % 6 = 2 ∨ v % 6 = 4) :
    ∃ R : Finset (Finset (Finset (Fin (2^m*v)))),
      (∀ D ∈ R, D.IsBlockDesign 3 4) ∧
      (R : Set (Finset (Finset (Fin (2^m*v))))).Pairwise (fun D E => ¬Isomorphic D E) ∧
      labelledCount v * 2^(switchExponent v m) ≤ R.card * (2^m*v).factorial ∧
      2^(switchExponent v m - Nat.clog 2 (2^m*v).factorial) ≤ R.card := by
  obtain ⟨H,hH⟩ := (Fourfold.quadruple_spectrum v).mpr hv
  exact many_representatives v m ⟨H,hH⟩

theorem order_sixty_four : ∃ R : Finset (Finset (Finset (Fin 64))),
    (∀ D ∈ R, D.IsBlockDesign 3 4) ∧
    (R : Set (Finset (Finset (Fin 64)))).Pairwise (fun D E => ¬Isomorphic D E) ∧
    2^1099 ≤ R.card := by
  obtain ⟨R,sys,pair,_,lower⟩ := admissible_orders 4 4 (by decide)
  have exp : switchExponent 4 4 - Nat.clog 2 (2^4*4).factorial = 1099 := by decide +kernel
  exact ⟨R,sys,pair,exp ▸ lower⟩

#print axioms sharp_switch
#print axioms exponent_identity
#print axioms admissible_orders
#print axioms order_sixty_four
end Erdos722.QuadSwitch
