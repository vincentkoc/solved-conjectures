import LucasFibonacciSquareValues

/-! The square class of seven on the two neighboring Hosoya diagonals. -/

namespace Arxiv.«2211.10788»

private theorem lower_step (n : ℕ) : lowerNeighborAtAddTwo (n+2) =
    lowerNeighborAtAddTwo n + lowerNeighborAtAddTwo (n+1) := by
  simp only [lowerNeighborAtAddTwo, Nat.fib_add_two]
  omega

private theorem cycle_sixteen (s : ℕ → ℕ) (d : ℕ)
    (hs : ∀ i, s (i+2) = s i + s (i+1))
    (h₀ : s 16 ≡ s 0 [MOD d]) (h₁ : s 17 ≡ s 1 [MOD d]) (n : ℕ) :
    s n ≡ s (n%16) [MOD d] := by
  have shift (i : ℕ) : s (i+16) ≡ s i [MOD d] := by
    induction i using Nat.twoStepInduction with
    | zero => exact h₀
    | one => exact h₁
    | more i a b =>
      rw [show i+2+16=i+16+2 by omega, hs (i+16), hs i]
      exact a.add b
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 16
    · rw [Nat.mod_eq_of_lt hn]
    · let i := n-16
      have he : n=i+16 := by dsimp [i]; omega
      have hi : i<n := by omega
      rw [he, Nat.add_mod_right]
      exact (shift i).trans (ih i hi)

/-- The upper diagonal never equals seven times an integral square. -/
theorem upper_ne_seven_mul_square (n y : ℕ) : lucasFibonacciSum n ≠ 7*y^2 := by
  intro he
  have per := cycle_sixteen lucasFibonacciSum 21
    (fun i => (lucas_fibonacci_sum_recurrence i).trans (Nat.add_comm ..)) (by decide) (by decide) n
  have ht : ∀ i : Fin 16, ∀ z : ZMod 21,
      (lucasFibonacciSum i : ZMod 21) ≠ 7*z^2 := by decide
  apply ht ⟨n%16,Nat.mod_lt _ (by decide)⟩ (y : ZMod 21)
  rw [←(ZMod.natCast_eq_natCast_iff ..).mpr per,he]
  push_cast
  rfl

private theorem lower_cycle (n : ℕ) :
    lowerNeighborAtAddTwo n ≡ lowerNeighborAtAddTwo (n%16) [MOD 7] :=
  cycle_sixteen _ 7 lower_step (by decide) (by decide) n

private theorem exclude_later (a root d y : ℕ) (hd : d ≠ 0)
    (anchor : lowerNeighborAtAddTwo a = 7*root^2) (hr : root=1 ∨ root=7) :
    lowerNeighborAtAddTwo (a+16*d) ≠ 7*y^2 := by
  obtain ⟨j,t,ht,he⟩ := Nat.exists_eq_two_pow_mul_odd hd
  let r := 2+j
  have period : 4*2^r=16*2^j := by dsimp [r]; rw [pow_add]; ring
  obtain ⟨p,hp,hfour,flip⟩ := dyadic_sign_prime r
  let s := fun n => (lowerNeighborAtAddTwo n : ℤ)
  have recurs : ∀ i, s (i+2)=s i+s (i+1) := by
    intro i
    dsimp [s]
    exact_mod_cast lower_step i
  have pn : p≠7 := by
    rintro rfl
    have h := flip s recurs 0 1
    simp only [pow_one,mul_one,zero_add,s,Int.cast_natCast,neg_one_mul] at h
    rw [period] at h
    have per := (ZMod.natCast_eq_natCast_iff ..).mpr (lower_cycle (16*2^j))
    rw [Nat.mul_mod_right] at per
    rw [per] at h
    exact (by decide : (lowerNeighborAtAddTwo 0:ZMod 7) ≠ -lowerNeighborAtAddTwo 0) h
  have : Fact p.Prime := ⟨hp⟩
  have unit : (7:ZMod p) ≠ 0 := by
    change (↑(7:ℕ):ZMod p) ≠ 0
    exact mt (ZMod.natCast_eq_zero_iff ..).mp (fun h => pn ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  have root_unit : (root:ZMod p) ≠ 0 := by rcases hr with rfl|rfl <;> simp_all
  intro hy
  have eqn := flip s recurs a t
  simp only [s,period,Nat.mul_assoc,←he,hy,anchor,ht.neg_one_pow,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,neg_one_mul] at eqn
  push_cast at eqn
  have neg : (y:ZMod p)^2=-(root:ZMod p)^2 := by
    apply mul_left_cancel₀ unit
    linear_combination eqn
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' root_unit neg hfour

/-- At physical index m+2 the lower value is seven times a square precisely
at indices four and twelve, with square roots one and seven respectively. -/
theorem lower_eq_seven_mul_square_iff (m y : ℕ) :
    lowerNeighborAtAddTwo m=7*y^2 ↔ (m=2 ∧ y=1) ∨ (m=10 ∧ y=7) := by
  constructor
  · intro he
    have table : ∀ i : Fin 16, lowerNeighborAtAddTwo i % 7=0 → i.val=2 ∨ i.val=10 := by decide
    have hz : lowerNeighborAtAddTwo (m%16)%7=0 := by
      rw [←(lower_cycle m : lowerNeighborAtAddTwo m%7 = _), he, Nat.mul_mod_right]
    rcases table ⟨m%16,Nat.mod_lt _ (by decide)⟩ hz with h|h
    · change m%16=2 at h
      by_cases hm : m=2
      · subst m
        change 7=7*y^2 at he
        left; exact ⟨rfl,by nlinarith⟩
      · have hd : m/16 ≠ 0 := by omega
        have hx : m=2+16*(m/16) := by omega
        exact False.elim (exclude_later 2 1 (m/16) y hd (by decide) (Or.inl rfl) (hx ▸ he))
    · change m%16=10 at h
      by_cases hm : m=10
      · subst m
        change 343=7*y^2 at he
        right; exact ⟨rfl,by nlinarith⟩
      · have hd : m/16 ≠ 0 := by omega
        have hx : m=10+16*(m/16) := by omega
        exact False.elim (exclude_later 10 7 (m/16) y hd (by decide) (Or.inr rfl) (hx ▸ he))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> decide

#print axioms upper_ne_seven_mul_square
#print axioms lower_eq_seven_mul_square_iff

end Arxiv.«2211.10788»
