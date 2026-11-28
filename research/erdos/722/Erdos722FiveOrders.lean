import Mathlib.Tactic

/-!
# Arithmetic closure for five-point pair designs

A bit at position `u` records a master design on `u` points. Truncating
a transversal design gives `5t+r`; adjoining a shared point gives `5t+r+1`.
The finite certificate below uses these two operations on four seed sizes.
-/

namespace Erdos722.Five

def Good (t : ℕ) : Prop := t % 6 = 1 ∨ t % 6 = 5 ∨ t = 9 ∨ t = 16

instance (t : ℕ) : Decidable (Good t) := by unfold Good; infer_instance

private def seeds : ℕ := 2^0 ||| 2^1 ||| 2^5 ||| 2^6 ||| 2^10 ||| 2^16

private def more (s t a : ℕ) : ℕ :=
  if s.testBit (t+a) then (((s >>> a) % 2^(t+1)) <<< (5*t+a)) else 0

private def step (s t : ℕ) : ℕ :=
  if Good t then s ||| more s t 0 ||| more s t 1 else s

private def table : ℕ → ℕ
  | 0 => seeds
  | n+1 => step (table n) (n+1)

private def mask : ℕ → ℕ
  | 0 => 0
  | n+1 => mask n ||| (3 <<< (5*n))

private theorem mask_bit {m i : ℕ} (hi : i < 5*m) (hr : i%5 ≤ 1) :
    (mask m).testBit i := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [mask,Nat.testBit_or,Bool.or_eq_true]
    by_cases h : i < 5*m
    · exact Or.inl (ih h)
    · right
      rw [Nat.testBit_shiftLeft]
      have h0 : i = 5*m ∨ i = 5*m+1 := by omega
      rcases h0 with rfl | rfl <;> simp
      decide

section
variable (P : ℕ → Prop) (small : ∀ i, i=0 ∨ i=1 ∨ i=5 ∨ i=6 ∨ i=10 ∨ i=16 → P i)
variable (grow : ∀ t r a, Good t → r ≤ t → a ≤ 1 → P (t+a) → P (r+a) → P (5*t+r+a))

include small in
private theorem seed_sound {i : ℕ} (h : seeds.testBit i) : P i := by
  apply small
  simpa only [seeds,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,
    eq_comm (a := i),or_assoc] using h

include grow in
private theorem more_sound {s t a i : ℕ} (ht : Good t) (ha : a ≤ 1)
    (hs : ∀ j, s.testBit j → P j) (hi : (more s t a).testBit i) : P i := by
  unfold more at hi
  split at hi
  next htbit =>
    simp only [Nat.testBit_shiftLeft,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,
      Bool.and_eq_true,decide_eq_true_eq] at hi
    obtain ⟨hle,hlt,hrbit⟩ := hi
    let r := i-(5*t+a)
    have hr : r ≤ t := by dsimp [r]; omega
    have he : i=5*t+r+a := by dsimp [r]; omega
    rw [he]
    exact grow t r a ht hr ha (hs _ htbit) (by simpa [r,Nat.add_comm] using hs _ hrbit)
  next => simp at hi

include small grow in
private theorem table_sound (n i : ℕ) (hi : (table n).testBit i) : P i := by
  induction n generalizing i with
  | zero => exact seed_sound P small hi
  | succ n ih =>
    unfold table step at hi
    split at hi
    next h =>
      simp only [Nat.testBit_or,Bool.or_eq_true] at hi
      rcases hi with (hi | hi) | hi
      · exact ih _ hi
      · exact more_sound P grow h (by decide : 0≤1) ih hi
      · exact more_sound P grow h (by decide : 1≤1) ih hi
    next => exact ih _ hi

set_option maxRecDepth 50000 in
set_option maxHeartbeats 8000000 in
private theorem covered :
    table 4100 &&& (mask 3460 <<< 3200) = mask 3460 <<< 3200 := by decide +kernel

include small grow in
private theorem initial {u : ℕ} (hu : 3200 ≤ u) (hU : u < 20500) (hr : u%5 ≤ 1) : P u := by
  apply table_sound P small grow 4100 u
  have hm : (mask 3460 <<< 3200).testBit u := by
    rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
    exact ⟨decide_eq_true hu,mask_bit (by omega) (by omega)⟩
  have eq := congrArg (fun s : ℕ => s.testBit u) covered
  simpa [Nat.testBit_and,hm] using eq

include small grow in
/-- A finite collection of master designs and transversal fillings suffices
at every admissible group count from 3200 onward. -/
theorem eventual_orders (u : ℕ) (hu : 3200 ≤ u) (hr : u%5 ≤ 1) : P u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases h : u < 20500
    · exact initial P small grow hu h hr
    · let t := 30*(u/180)+31
      let r := u-5*t
      have ht : Good t := Or.inl (by dsimp [t]; omega)
      have ht0 : 3200 ≤ t := by dsimp [t]; omega
      have hr0 : 3200 ≤ r := by dsimp [r,t]; omega
      have hrt : r ≤ t := by dsimp [r,t]; omega
      have ht5 : t%5 ≤ 1 := by dsimp [t]; omega
      have hr5 : r%5 ≤ 1 := by dsimp [r,t]; omega
      have he : 5*t+r+0 = u := by dsimp [r,t]; omega
      exact he ▸ grow t r 0 ht hrt (by decide)
        (by simpa using ih t (by dsimp [t]; omega) ht0 ht5)
        (by simpa using ih r (by dsimp [r,t]; omega) hr0 hr5)

#print axioms eventual_orders

end
end Erdos722.Five
