import Mathlib

/-! Coefficient lists at the two ends of a polynomial and their autocorrelations. -/

namespace CunninghamChain.CoefficientSlices
open Polynomial

def slice (n : ℕ) (v : ℕ → ℤ) := (List.range n).map v
def dot (a b : List ℤ) : ℤ := (List.zipWith (·*·) a b).sum
def squaredNorm (xs : List ℤ) : ℕ := (xs.map (fun z => z.natAbs^2)).sum

lemma slice_sum (n : ℕ) (v : ℕ → ℤ) :
    (slice n v).sum = ∑ i ∈ Finset.range n, v i := by
  induction n with
  | zero => simp [slice]
  | succ n ih => simp [slice,List.range_succ,Finset.sum_range_succ] at ih ⊢; exact ih

lemma slice_ext (n : ℕ) (v u : ℕ → ℤ) (h : ∀ i < n, v i = u i) :
    slice n v = slice n u := by
  apply List.ext_getElem
  · simp [slice]
  · intro i hi _
    simpa [slice] using h i (by simpa [slice] using hi)

lemma slice_reverse (n : ℕ) (v : ℕ → ℤ) :
    (slice n v).reverse = slice n (fun i => v (n-1-i)) := by
  apply List.ext_getElem
  · simp [slice]
  · intro i h₁ h₂
    simp [slice,List.getElem_reverse]

lemma slice_drop (k n : ℕ) (v : ℕ → ℤ) :
    (slice n v).drop k = slice (n-k) (fun i => v (k+i)) := by
  apply List.ext_getElem
  · simp [slice]
  · intro i h₁ h₂
    simp [slice]

lemma slice_add (k n : ℕ) (v : ℕ → ℤ) :
    slice (k+n) v = slice k v ++ slice n (fun i => v (k+i)) := by
  simp only [slice,List.range_add,List.map_append,List.map_map,Function.comp_def]

lemma dot_slices (n m : ℕ) (v u : ℕ → ℤ) :
    dot (slice n v) (slice m u) = ∑ i ∈ Finset.range (min n m), v i*u i := by
  rw [← slice_sum]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp [slice]
  · intro i h₁ h₂
    simp [slice]

/-- The low coefficient of the product with its reflection reads from opposite ends. -/
lemma correlation (g : ℤ[X]) (N n : ℕ) (hn : n ≤ N) :
    (g * reflect N g).coeff n =
      ∑ i ∈ Finset.range (n+1), g.coeff (n-i) * g.coeff (N-i) := by
  rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => (reflect N g).coeff i*g.coeff k)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_reflect,revAt_le ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn),mul_comm]

lemma slice_succ (n : ℕ) (v : ℕ → ℤ) :
    slice (n+1) v = slice n v ++ [v n] := by simp [slice,List.range_succ]
lemma slice_cons (n : ℕ) (v : ℕ → ℤ) :
    slice (n+1) v = v 0 :: slice n (fun i => v (1+i)) := by
  rw [Nat.add_comm n 1,slice_add]
  rfl

-- The two stored prefixes have their innermost coefficients first.
def low (v : ℕ → ℤ) (n : ℕ) := (slice n v).reverse
def high (N : ℕ) (v : ℕ → ℤ) (n : ℕ) := (slice n (fun i => v (N-i))).reverse
def middle (N : ℕ) (v : ℕ → ℤ) (n : ℕ) :=
  slice (N+1-n-n) (fun i => v (n+i))

lemma split_slice (N n : ℕ) (hn : n+n ≤ N+1) (v : ℕ → ℤ) :
    slice (N+1) v = (low v n).reverse ++ middle N v n ++ high N v n := by
  let m := N+1-n-n
  have he : n+m+n=N+1 := by dsimp [m]; omega
  calc
    slice (N+1) v = slice (n+m) v ++ slice n (fun i => v ((n+m)+i)) := he ▸ slice_add _ _ _
    _ = _ := by
      rw [slice_add]
      simp only [low,List.reverse_reverse,middle,high]
      rw [slice_reverse]
      apply congrArg (fun z => (slice n v ++ slice m (fun i => v (n+i))) ++ z)
      apply slice_ext
      intro i hi
      congr 1
      dsimp [m]
      omega

lemma middle_step (N n : ℕ) (v : ℕ → ℤ) (hn : n+n+2 ≤ N+1) :
    middle N v n = v n :: (middle N v (n+1) ++ [v (N-n)]) := by
  let m := N+1-(n+1)-(n+1)
  have he : N+1-n-n=m+1+1 := by dsimp [m]; omega
  unfold middle
  rw [he,slice_succ,slice_cons]
  simp only [Nat.add_zero,List.cons_append,List.cons.injEq,true_and]
  congr 1
  · apply slice_ext
    intro i hi
    congr 1
    omega
  · dsimp [m]
    congr 2
    omega

lemma prefix_relation (N n : ℕ) (v : ℕ → ℤ) (hn : 0 < n) (hN : n ≤ N)
    :
    ∑ i ∈ Finset.range (n+1), v (n-i)*v (N-i) =
      v 0*v (N-n)+v N*v n+dot (low v n) (high N v n).reverse.tail := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  simp only [Nat.sub_self,Nat.sub_zero,high,List.reverse_reverse]
  rw [slice_cons k (fun i => v (N-i)),List.tail_cons]
  simp only [low,slice_reverse,dot_slices,Nat.min_eq_right (by omega : k ≤ k+1)]
  have hx : ∑ i ∈ Finset.range k, v (k+1-(i+1))*v (N-(i+1)) =
      ∑ i ∈ Finset.range k, v (k+1-1-i)*v (N-(1+i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm 1 i,show k+1-(i+1)=k+1-1-i by omega]
  linear_combination hx

lemma squaredNorm_cons (v : ℤ) (a : List ℤ) :
    squaredNorm (v::a) = v.natAbs^2 + squaredNorm a := by simp [squaredNorm]

lemma squaredNorm_append (a b : List ℤ) :
    squaredNorm (a++b) = squaredNorm a + squaredNorm b := by simp [squaredNorm]

lemma squaredNorm_cast (a : List ℤ) : (squaredNorm a : ℤ) = dot a a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    rw [squaredNorm_cons,Nat.cast_add,Nat.cast_pow,Int.natCast_natAbs,sq_abs,ih]
    simp [dot,pow_two]

lemma full_lag (N h : ℕ) (hh : h ≤ N) (g : ℤ[X]) :
    dot (slice (N+1) g.coeff) ((slice (N+1) g.coeff).drop h) =
      (g*reflect N g).coeff (N-h) := by
  rw [slice_drop,dot_slices,Nat.min_eq_right (Nat.sub_le ..)]
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => g.coeff i*(reflect N g).coeff k)]
  rw [show N+1-h=N-h+1 by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [coeff_reflect,revAt_le (by omega),show N-(N-h-i)=h+i by omega]

#print axioms prefix_relation
#print axioms full_lag

end CunninghamChain.CoefficientSlices
