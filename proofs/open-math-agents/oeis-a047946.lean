import OMAStatements.S_oeis_a047946
import Mathlib

-- Problem: A047946: a(n) = 5*F(n)^2 + 3*(-1)^n where F(n) are the Fibonacci numbers A000045.
-- Upstream: formal-conjectures statements/oeis-a047946.lean:0 (declaration OMA.S_oeis_a047946.main)
-- Credit: @vincentkoc (the owner of the agent is credited as the solver)
-- Proof: Binet's formula. With u = φ^n and v = ψ^n (so u * v = (-1)^n), the squares
-- F(n k)^2 = (u^k - v^k)^2 / 5 lie in the span of u^(2k), v^(2k), (u v)^k, whose roots
-- u^2, v^2, (-1)^n have sum 5 F(n)^2 + 3 (-1)^n; the recurrence is then a polynomial identity.

open Real in
theorem OMA.solution : type_of% @OMA.S_oeis_a047946.main := by
  intro n _ k
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hF : ∀ j : ℕ, ((n * j).fib : ℝ) =
      ((goldenRatio ^ n) ^ j - (goldenConj ^ n) ^ j) / Real.sqrt 5 := by
    intro j
    rw [Real.coe_fib_eq, pow_mul, pow_mul]
  have hFn : (n.fib : ℝ) = (goldenRatio ^ n - goldenConj ^ n) / Real.sqrt 5 := by
    simpa using hF 1
  have huv : goldenRatio ^ n * goldenConj ^ n = (-1 : ℝ) ^ n := by
    rw [← mul_pow, goldenRatio_mul_goldenConj]
  apply Int.cast_injective (α := ℝ)
  simp only [OMA.S_oeis_a047946.fibSquare, OMA.S_oeis_a047946.coefficient]
  set u : ℝ := goldenRatio ^ n
  set v : ℝ := goldenConj ^ n
  split_ifs with h
  · have hw : (-1 : ℝ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr h)
    rw [hw] at huv
    push_cast
    rw [hF, hF, hF, hF, hFn, hw]
    simp only [div_pow, hs]
    linear_combination
      (2*(u^k)^2*u^4/5 - (u^k)^2*u^3*v/5 + 3*(u^k)^2*u^2/5 - (u^k)^2*u*v/5 + (u^k)^2/5
        + 2*(u^k)*(v^k)*u^3*v/5 - 6*(u^k)*(v^k)*u^2*v^2/5 + 2*(u^k)*(v^k)*u*v^3/5
        - 4*(u^k)*(v^k)*u*v/5 - 2*(u^k)*(v^k)/5 - (v^k)^2*u*v^3/5 - (v^k)^2*u*v/5
        + 2*(v^k)^2*v^4/5 + 3*(v^k)^2*v^2/5 + (v^k)^2/5) * huv
  · have hw : (-1 : ℝ) ^ n = 1 :=
      Even.neg_one_pow (Nat.even_iff.mpr (by omega))
    rw [hw] at huv
    push_cast
    rw [hF, hF, hF, hF, hFn, hw]
    simp only [div_pow, hs]
    linear_combination
      (2*(u^k)^2*u^4/5 - (u^k)^2*u^3*v/5 - 3*(u^k)^2*u^2/5 + (u^k)^2*u*v/5 + (u^k)^2/5
        + 2*(u^k)*(v^k)*u^3*v/5 - 6*(u^k)*(v^k)*u^2*v^2/5 + 2*(u^k)*(v^k)*u*v^3/5
        + 4*(u^k)*(v^k)*u*v/5 - 2*(u^k)*(v^k)/5 - (v^k)^2*u*v^3/5 + (v^k)^2*u*v/5
        + 2*(v^k)^2*v^4/5 - 3*(v^k)^2*v^2/5 + (v^k)^2/5) * huv
