import Mathlib

/-! The norm of a gap in a Fibonacci recurrence is a Fibonacci square times its Cassini invariant. -/
namespace Arxiv.«2211.10788».PowerGaps
open Real
open scoped goldenRatio

private lemma displacement (f : ℕ → ℝ) (step : ∀ n, f (n+2)=f (n+1)+f n)
    (n : ℕ) (α : ℝ) (quad : α^2=α+1) (h : ℕ) :
    f (n+h)-α^h*f n=Nat.fib h*(f (n+1)-α*f n) := by
  induction h using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more h ih0 ih1 =>
    have powStep : α^(h+2)=α^(h+1)+α^h := by rw [pow_add,quad,pow_succ];ring
    rw [←Nat.add_assoc,step (n+h),powStep,Nat.fib_add_two,Nat.cast_add]
    rw [Nat.add_assoc n h 1]
    linarith

private lemma abs_invariant (f : ℕ → ℝ) (step : ∀ n, f (n+2)=f (n+1)+f n) (n : ℕ) :
    |f (n+1)^2 - f (n+1)*f n - f n^2| = |f 1^2 - f 1*f 0 - f 0^2| := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,step]
    convert ih using 1
    rw [←abs_neg (f (n+1)^2 - f (n+1)*f n - f n^2)]
    congr 1; ring

theorem gap_norm (f : ℕ → ℝ) (step : ∀ n, f (n+2)=f (n+1)+f n) (n h : ℕ) :
    |(f (n+h)-φ^h*f n)*(f (n+h)-ψ^h*f n)| =
      (Nat.fib h:ℝ)^2*|f 1^2 - f 1*f 0 - f 0^2| := by
  rw [displacement f step n φ goldenRatio_sq,displacement f step n ψ goldenConj_sq]
  have eq : (f (n+1)-φ*f n)*(f (n+1)-ψ*f n) =
      f (n+1)^2 - f (n+1)*f n - f n^2 := by
    calc
      _ = f (n+1)^2-(φ+ψ)*f (n+1)*f n+(φ*ψ)*f n^2 := by ring
      _ = _ := by rw [goldenRatio_add_goldenConj,goldenRatio_mul_goldenConj];ring
  rw [show (Nat.fib h:ℝ)*(f (n+1)-φ*f n)*(Nat.fib h*(f (n+1)-ψ*f n))=
    (Nat.fib h:ℝ)^2*((f (n+1)-φ*f n)*(f (n+1)-ψ*f n)) by ring,abs_mul,
    abs_of_nonneg (sq_nonneg _),eq,abs_invariant f step n]

#print axioms gap_norm
end Arxiv.«2211.10788».PowerGaps
