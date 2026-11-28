import LucasFibonacciCongruenceClosure
import Mathlib.Algebra.Ring.Periodic

/-! Lucas shifts and reflection for the bilateral upper Hosoya sequence. -/

namespace Arxiv.«2211.10788».ProgressionClosure

open CongruenceClosure

/-- The ordinary Lucas number expressed in terms of its Fibonacci neighbors. -/
def lucas (h : ℕ) : ℕ := 2 * Nat.fib (h+1) - Nat.fib h

lemma lucas_cast (h : ℕ) :
    (lucas h : ℤ) = 2 * (Nat.fib (h+1) : ℤ) - Nat.fib h := by
  have := Nat.fib_mono (show h ≤ h+1 by omega)
  unfold lucas
  push_cast [show Nat.fib h ≤ 2 * Nat.fib (h+1) by omega]
  rfl

private lemma signed_step (z : ℤ) : signed (z+2) = signed z + signed (z+1) := by
  unfold signed
  rw [Int.fib_add_two (z+2), Int.fib_add_two z]
  ring_nf

private lemma signed_shift (z : ℤ) (h : ℕ) :
    signed (z+h) = ((Nat.fib (h+1):ℤ)-Nat.fib h)*signed z + Nat.fib h*signed (z+1) := by
  have prev := Int.fib_add_two ((h:ℤ)-1)
  rw [show (h:ℤ)-1+2 = ((h+1:ℕ):ℤ) by push_cast; ring, sub_add_cancel,
    Int.fib_natCast,Int.fib_natCast] at prev
  have add (v : ℤ) : Int.fib (v+h) =
      ((Nat.fib (h+1):ℤ)-Nat.fib h)*Int.fib v + Nat.fib h * Int.fib (v+1) := by
    rw [add_comm v,Int.fib_add,Int.fib_natCast,show Int.fib ((h:ℤ)-1) = (Nat.fib (h+1):ℤ) - Nat.fib h by omega]
  unfold signed
  rw [show z+h+2 = z+2+h by ring, add, add, show z+1+2 = z+2+1 by ring]
  ring

private lemma determinant {h : ℕ} (he : Even h) :
    (Nat.fib (h+1) : ℤ)^2 - Nat.fib h * Nat.fib (h+1) - (Nat.fib h : ℤ)^2 = 1 := by
  rw [fib_pair_norm,he.neg_one_pow]

lemma trace_norm {h : ℕ} (he : Even h) :
    (lucas h : ℤ)^2 - 5*(Nat.fib h : ℤ)^2 = 4 := by
  rw [lucas_cast]
  linear_combination 4*determinant he

lemma half_shift (z : ℤ) (h : ℕ) :
    2*signed (z+h) = lucas h * signed z + Nat.fib h*(2*signed (z+1)-signed z) := by
  rw [signed_shift,lucas_cast]
  ring

private lemma double_shift (z : ℤ) {h : ℕ} (he : Even h) :
    signed (z+2*h) = lucas h * signed (z+h) - signed z := by
  rw [show z+2*h = z+h+h by ring,signed_shift (z+h),show z+h+1 = z+1+h by ring,
    signed_shift (z+1),signed_shift z,show z+1+1=z+2 by ring,signed_step,lucas_cast]
  linear_combination -(signed z) * determinant he

/-- Translation by twice an even index negates the sequence modulo its Lucas number. -/
theorem lucas_antiperiod (z : ℤ) {h : ℕ} (he : Even h) :
    (signed (z+2*h) : ZMod (lucas h)) = -(signed z : ZMod (lucas h)) := by
  rw [double_shift z he]
  simp

theorem lucas_period {h : ℕ} (he : Even h) :
    Function.Periodic (fun z : ℤ => (signed z : ZMod (lucas h))) (4*(h:ℤ)) := by
  intro z
  change (signed (z+4*h) : ZMod (lucas h)) = signed z
  rw [show z+4*h = z+2*h+2*h by ring, lucas_antiperiod _ he,lucas_antiperiod _ he,neg_neg]

#print axioms trace_norm
#print axioms half_shift
#print axioms lucas_antiperiod
#print axioms lucas_period

end Arxiv.«2211.10788».ProgressionClosure
