import Mathlib

/-! Simultaneous compression of integer sites preserving pair-sum comparisons. -/

open Finset

namespace Green28SupportCompression

private noncomputable def box (u : ℝ) : Fin 5 :=
  ⟨⌊5 * Int.fract u⌋₊, (Nat.floor_lt (by positivity)).mpr (by
    have := Int.fract_lt_one u
    norm_num
    linarith)⟩

private theorem box_error {u v : ℝ} (h : box u = box v) :
    |(u-v) - (↑(⌊u⌋-⌊v⌋) : ℝ)| < 1/5 := by
  have e : ⌊5 * Int.fract u⌋₊ = ⌊5 * Int.fract v⌋₊ := congrArg Fin.val h
  have lu := Nat.floor_le (show 0 ≤ 5 * Int.fract u by positivity)
  have lv := Nat.floor_le (show 0 ≤ 5 * Int.fract v by positivity)
  have hu := Nat.lt_floor_add_one (5 * Int.fract u)
  have hv := Nat.lt_floor_add_one (5 * Int.fract v)
  rw [e] at lu hu
  push_cast
  have eu := Int.self_sub_floor u
  have ev := Int.self_sub_floor v
  rw [abs_lt]
  constructor <;> linarith

/-- A common positive denominator works for all coordinates, with strict error. -/
theorem simultaneous_fifths {n : ℕ} (x : Fin n → ℝ) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 5^n ∧ ∃ b : Fin n → ℤ, ∀ i, |q*x i - b i| < 1/5 := by
  let tag (t : Fin (5^n+1)) (i : Fin n) := box (t.val * x i)
  obtain ⟨u,v,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by simp)
  have step {u v : Fin (5^n+1)} (lt : v<u) (eq : tag u=tag v) :
      ∃ q : ℕ, 0 < q ∧ q ≤ 5^n ∧ ∃ b : Fin n → ℤ, ∀ i, |q*x i - b i| < 1/5 := by
    have lt' : v.val < u.val := lt
    refine ⟨u.val-v.val, by omega, by have := u.isLt; omega,
      fun i => ⌊u.val*x i⌋ - ⌊v.val*x i⌋, fun i => ?_⟩
    rw [Nat.cast_sub lt'.le, sub_mul]
    exact box_error (congrFun eq i)
  rcases lt_or_gt_of_ne ne with hv|hu
  · exact step hv eq.symm
  · exact step hu eq

/-- Affine rounding with error below one fifth preserves all pair-sum comparisons
at scales greater than four fifths. -/
private theorem compare {n : ℕ} {a b : Fin n → ℤ} {c : ℝ} (hc : 4/5 < c)
    (err : ∀ i, |(b i : ℝ)-c*a i| < 1/5) (i j k l : Fin n) :
    a i+a j ≤ a k+a l ↔ b i+b j ≤ b k+b l := by
  have gap {i j k l : Fin n} (lt : a i+a j < a k+a l) : b i+b j < b k+b l := by
    have unit : (1 : ℝ) ≤ (a k : ℝ)+a l-a i-a j := by exact_mod_cast (by omega : 1 ≤ a k+a l-a i-a j)
    have sep := mul_le_mul_of_nonneg_left unit (by linarith : 0 ≤ c)
    apply (Int.cast_lt (R := ℝ)).mp
    push_cast
    linarith [(abs_lt.mp (err i)).2,(abs_lt.mp (err j)).2,
      (abs_lt.mp (err k)).1,(abs_lt.mp (err l)).1]
  constructor
  · intro le
    rcases le.lt_or_eq with lt|eq
    · exact (gap lt).le
    · by_contra! he
      have jump : (1 : ℝ) ≤ (b i : ℝ)+b j-b k-b l := by exact_mod_cast (by omega : 1 ≤ b i+b j-b k-b l)
      have flat := congrArg (fun t : ℤ => c*(t:ℝ)) eq
      push_cast at flat
      linarith [(abs_lt.mp (err i)).2,(abs_lt.mp (err j)).2,
        (abs_lt.mp (err k)).1,(abs_lt.mp (err l)).1]
  · intro le
    by_contra! he
    exact (gap he).not_ge le

/-- If the ambient interval exceeds the cutoff then it can be made strictly
shorter while retaining the order and coincidences of every pair of sums. -/
theorem contract {n D : ℕ} (large : 5^(n+1) < D) (a : Fin n → ℤ)
    (range : ∀ i, 0 ≤ a i ∧ a i ≤ D) :
    ∃ E < D, ∃ b : Fin n → ℤ, (∀ i, 0 ≤ b i ∧ b i ≤ E) ∧
      ∀ i j k l, a i+a j ≤ a k+a l ↔ b i+b j ≤ b k+b l := by
  obtain ⟨q,hq,hmax,u,hu⟩ := simultaneous_fifths (fun i => (a i : ℝ)/D)
  have q5 : 5*q < D := by rw [pow_succ] at large; omega
  have dpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let c : ℝ := 1 - (q:ℝ)/D
  have cs : 4/5 < c := by
    have qr : (q:ℝ)/D < 1/5 := (div_lt_iff₀ dpos).mpr (by
      have : (5:ℝ)*q < D := by exact_mod_cast q5
      linarith)
    dsimp [c]; linarith
  let b (i : Fin n) := a i-u i
  have err (i) : |(b i : ℝ)-c*a i| < 1/5 := by
    convert hu i using 2
    dsimp [b,c]
    push_cast
    ring
  have rE : (↑(D-q) : ℝ) = c*D := by
    rw [Nat.cast_sub (by omega)]
    dsimp [c]
    field_simp
  refine ⟨D-q, by omega,b,?_,compare cs err⟩
  intro i
  have ar : (0:ℝ) ≤ a i := by exact_mod_cast (range i).1
  have adr : (a i : ℝ) ≤ D := by exact_mod_cast (range i).2
  have cn : 0 ≤ c := by linarith
  constructor
  · by_contra! h
    have neg : (b i : ℝ) ≤ -1 := by exact_mod_cast (by omega : b i ≤ -1)
    linarith [(abs_lt.mp (err i)).1, mul_nonneg cn ar]
  · by_contra! h
    have up : (↑(D-q) : ℝ)+1 ≤ b i := by exact_mod_cast (by omega : (↑(D-q):ℤ)+1 ≤ b i)
    linarith [(abs_lt.mp (err i)).2, mul_le_mul_of_nonneg_left adr cn]

/-- The bound depends on the number of labelled sites and allows repeated sites.
It preserves all weak inequalities, so it also preserves every collision. -/
theorem bounded_sites {n D : ℕ} (a : Fin n → ℤ) (range : ∀ i, 0 ≤ a i ∧ a i ≤ D) :
    ∃ b : Fin n → ℤ, (∀ i, 0 ≤ b i ∧ b i ≤ (5^(n+1) : ℕ)) ∧
      ∀ i j k l, a i+a j ≤ a k+a l ↔ b i+b j ≤ b k+b l := by
  induction D using Nat.strong_induction_on generalizing a with
  | h D ih =>
    by_cases small : D ≤ 5^(n+1)
    · exact ⟨a, fun i => ⟨(range i).1,(range i).2.trans (by exact_mod_cast small)⟩,
        fun _ _ _ _ => Iff.rfl⟩
    · obtain ⟨E,smaller,b,br,rel⟩ := contract (lt_of_not_ge small) a range
      obtain ⟨c,cr,re⟩ := ih E smaller b br
      exact ⟨c,cr,fun i j k l => (rel i j k l).trans (re i j k l)⟩

#print axioms simultaneous_fifths
#print axioms contract
#print axioms bounded_sites

end Green28SupportCompression
