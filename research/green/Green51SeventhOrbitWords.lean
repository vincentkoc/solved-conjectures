import Mathlib

/-! # Binary words satisfying the length-73 cyclic recurrence -/

namespace Green51SeventhOrbit

private def weight : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, a :: b :: tail => a.toNat + weight n (b :: (tail ++ [a ^^ b]))
  | _ + 1, _ => 0

set_option maxHeartbeats 1200000 in
private theorem weight_bound :
    ∀ a b c d e f g h i : Bool, weight 73 [a,b,c,d,e,f,g,h,i] ≤ 40 := by
  decide +kernel

private def window (s : ℕ → Bool) (j : ℕ) : List Bool :=
  [s j, s (j+1), s (j+2), s (j+3), s (j+4), s (j+5), s (j+6), s (j+7), s (j+8)]

/-- A binary sequence satisfying s(j+9) = s(j)+s(j+1) has at most forty
ones in any seventy-three consecutive positions. -/
theorem recurrence_weight (s : ℕ → Bool) (rec : ∀ i, s (i+9) = (s i ^^ s (i+1))) (j : ℕ) :
    ∑ i ∈ Finset.range 73, (s (j+i)).toNat ≤ 40 := by
  have counted (n : ℕ) (k : ℕ) :
      weight n (window s k) = ∑ i ∈ Finset.range n, (s (k+i)).toNat := by
    induction n generalizing k with
    | zero => simp [weight]
    | succ n ih =>
      change (s k).toNat + weight n
        [s (k+1),s (k+2),s (k+3),s (k+4),s (k+5),s (k+6),s (k+7),s (k+8),s k ^^ s (k+1)] = _
      rw [← rec k]
      change (s k).toNat + weight n (window s (k+1)) = _
      rw [ih, Finset.sum_range_succ']
      simp [Nat.add_comm,Nat.add_left_comm]
  rw [← counted]
  exact weight_bound _ _ _ _ _ _ _ _ _

end Green51SeventhOrbit

#print axioms Green51SeventhOrbit.recurrence_weight
