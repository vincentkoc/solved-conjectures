import LucasFibonacciDiagonalUnion
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.GCDMonoid.Nat

/-! A single congruence test for the nonnegative values of the bilateral upper sequence. -/

namespace Arxiv.«2211.10788»
namespace CongruenceClosure

/-- The lower neighbors at the positive odd indices, beginning with 3 at index one. -/
def OddLowerValue (y : ℕ) : Prop :=
  y = 3 ∨ ∃ a, y = lowerNeighborAtAddTwo (2*a+1)

/-- Candidate-specific modulus for the two Pell discriminants and the orientation modulo 11. -/
def testModulus (y : ℕ) : ℕ :=
  if y < 3 then 11 else 11 * ((5*y^2+44)^2 * (5*y^2-44)^2)

private lemma minus_pos {y : ℕ} (hy : 3 ≤ y) : 44 < 5*y^2 := by nlinarith [Nat.mul_self_le_mul_self hy]

private lemma modulus_pos (y : ℕ) : 0 < testModulus y := by
  unfold testModulus
  split_ifs with h
  · decide
  · have := minus_pos (y := y) (by omega)
    exact Nat.mul_pos (by decide) (Nat.mul_pos (by positivity) (pow_pos (by omega) _))

/-- A positive integer is a square if a square is congruent to it modulo its own square. -/
theorem square_of_mod_self_sq {D x : ℕ} (hD : 0 < D) (hx : x^2 ≡ D [MOD D^2]) :
    ∃ a : ℕ, a^2 = D := by
  have hd : D ∣ D^2 := ⟨D, pow_two _⟩
  obtain ⟨c,hc⟩ := (hx.dvd_iff hd).mpr (dvd_refl D)
  have h1 : c ≡ 1 [MOD D] := Nat.ModEq.mul_left_cancel' hD.ne' (by
    simpa only [←hc,pow_two D,mul_one] using hx)
  have hg : IsUnit (gcd D c) := by
    change IsUnit (Nat.gcd D c)
    rw [Nat.gcd_comm, h1.gcd_eq]
    simp
  obtain ⟨a,ha⟩ := exists_eq_pow_of_mul_eq_pow hg hc.symm
  exact ⟨a,ha.symm⟩

/-- The canonical upper sum extended to all integer indices. -/
def signed (z : ℤ) : ℤ := 2 * Int.fib z + Int.fib (z+2)

lemma signed_nat (n : ℕ) : signed (n:ℤ) = (lucasFibonacciSum n : ℤ) := by
  simp only [signed,lucasFibonacciSum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.fib_natCast]
  rw [show (n:ℤ)+2 = ((n+2:ℕ):ℤ) by push_cast; rfl, Int.fib_natCast]

lemma signed_lower (m : ℕ) :
    signed (-((m+2:ℕ):ℤ)) = (-1:ℤ)^(m+1) * (lowerNeighborAtAddTwo m : ℤ) := by
  rw [signed,show -((m+2:ℕ):ℤ)+2 = -(m:ℤ) by push_cast; ring,
    Int.fib_neg_natCast,Int.fib_neg_natCast,lowerNeighborAtAddTwo]
  push_cast
  ring

private def shift {M : ℕ} (v : ZMod M × ZMod M) : ZMod M × ZMod M := (v.2, v.1 + v.2)

private lemma shift_injective (M : ℕ) : Function.Injective (shift (M := M)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ e
  obtain ⟨rfl,h⟩ := Prod.mk.inj (show (b,a+b) = (d,c+d) from e)
  exact Prod.ext (add_right_cancel h) rfl

private def state (M : ℕ) (z : ℤ) : ZMod M × ZMod M := (Int.fib z, Int.fib (z+1))

private lemma state_iterate (M : ℕ) (z : ℤ) (n : ℕ) :
    state M (z+n) = shift^[n] (state M z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ←ih]
    apply Prod.ext
    · simp [state, shift, Nat.cast_succ, add_assoc]
    · simp [state, shift, Nat.cast_succ, ←add_assoc, show ∀ a : ℤ, a+1+1=a+2 by intro a; ring,
        Int.fib_add_two]

private lemma read_state {M : ℕ} {z w : ℤ} (h : state M z = state M w) :
    (signed z : ZMod M) = signed w := by
  simpa [state,signed,Int.fib_add_two] using
    congrArg (fun v : ZMod M × ZMod M => 2*v.1+(v.1+v.2)) h

/-- Beyond a given signed index, its whole residue class modulo one
positive period gives the same upper value modulo M. -/
theorem signed_forward_period (M : ℕ) [NeZero M] (z : ℤ) :
    ∃ T : ℕ, 0<T ∧ ∀ n : ℤ, z≤n → n ≡ z [ZMOD T] → (signed n : ZMod M)=signed z := by
  obtain ⟨T,hT,fixed⟩ := (shift_injective M).mem_periodicPts (state M z)
  refine ⟨T,hT,?_⟩
  intro n big cl
  obtain ⟨v,eq⟩ := cl.symm.dvd
  have non : 0≤v := nonneg_of_mul_nonneg_right
    (show 0≤(T:ℤ)*v by linarith only [eq,big]) (by exact_mod_cast hT)
  have val : z+((v.toNat*T:ℕ):ℤ)=n := by
    push_cast
    rw [Int.toNat_of_nonneg non]
    linarith only [eq]
  rw [←val]
  exact read_state ((state_iterate M z _).trans (fixed.const_mul v.toNat).eq)

#print axioms signed_forward_period

private lemma negative_hit (M : ℕ) [NeZero M] (k : ℕ) :
    ∃ n, (lucasFibonacciSum n : ZMod M) = signed (-(k:ℤ)) := by
  let z := -(k:ℤ)
  obtain ⟨T,hT,hfix⟩ := (shift_injective M).mem_periodicPts (state M z)
  have hk : k ≤ k*T := Nat.le_mul_of_pos_right k hT
  have he : z+(k*T:ℕ) = ((k*T-k:ℕ):ℤ) := by dsimp [z]; push_cast [hk]; ring
  have hr := read_state ((state_iterate M z (k*T)).trans (hfix.const_mul k).eq)
  rw [he,signed_nat] at hr
  exact ⟨k*T-k,by simpa [z] using hr⟩

private lemma bounded_hit {M y : ℕ} [NeZero M] {n : ℕ} (h : lucasFibonacciSum n ≡ y [MOD M]) :
    ∃ j < M^2, lucasFibonacciSum j ≡ y [MOD M] := by
  let T := Function.minimalPeriod shift (state M 0)
  have hT : 0 < T := Function.minimalPeriod_pos_of_mem_periodicPts
    ((shift_injective M).mem_periodicPts (state M 0))
  have hcard : T ≤ M^2 := by
    simpa [T,Fintype.card_prod,ZMod.card,pow_two] using
      (Function.minimalPeriod_le_card (f := shift) (x := state M 0))
  refine ⟨n%T,(Nat.mod_lt _ hT).trans_le hcard,?_⟩
  apply Nat.ModEq.trans _ h
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  have hs : state M (0+(n%T:ℕ)) = state M (0+(n:ℕ)) := by
    rw [state_iterate,state_iterate]
    exact Function.iterate_mod_minimalPeriod_eq
  simpa only [zero_add,signed_nat,Int.cast_natCast] using read_state hs

lemma upper_mod_eleven (n : ℕ) : (lucasFibonacciSum n : ZMod 11) = 4^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,h₁,h₀,pow_add (4 : ZMod 11) n 2,
      pow_succ (4 : ZMod 11) n, show (4 : ZMod 11)^2 = 5 by decide]
    ring

/-- Every signed term has fifth power one modulo eleven. -/
theorem signed_fifth (z : ℤ) : (signed z : ZMod 11)^5 = 1 := by
  have h (n : ℕ) : (lucasFibonacciSum n : ZMod 11)^5 = 1 := by
    rw [upper_mod_eleven, ← pow_mul, mul_comm, pow_mul, show (4 : ZMod 11)^5 = 1 by decide, one_pow]
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa [signed_nat] using h n
  · obtain ⟨j,hj⟩ := negative_hit 11 n
    rw [←hj]
    exact h j

/-- A bilateral hit in a specified index class recurs on its nonnegative progression. -/
theorem signed_progression_hit (M d r : ℕ) [NeZero M] (c : ℤ) :
    ∃ t : ℕ, (lucasFibonacciSum (r+d*t) : ZMod M) = signed (r+d*c) := by
  let z : ℤ := r+d*c
  obtain ⟨T,hT,hfix⟩ := (shift_injective M).mem_periodicPts (state M z)
  let k := c.natAbs
  have hk : (k : ℤ) ≤ k*(T:ℤ) := by exact_mod_cast Nat.le_mul_of_pos_right k hT
  have hc : 0 ≤ c+k*(T:ℤ) := by dsimp [k] at *; omega
  let t := (c+k*T).toNat
  have ht : (t:ℤ) = c+k*T := Int.toNat_of_nonneg hc
  have he : z+((d*k*T:ℕ):ℤ) = ((r+d*t:ℕ):ℤ) := by dsimp [z]; rw [ht]; ring
  have hr := read_state ((state_iterate M z (d*k*T)).trans (hfix.const_mul (d*k)).eq)
  rw [he,signed_nat] at hr
  exact ⟨t,by simpa [z] using hr⟩

private lemma odd_lower_hit {y : ℕ} (hl : OddLowerValue y) (M : ℕ) [NeZero M] :
    ∃ n, lucasFibonacciSum n ≡ y [MOD M] := by
  rcases hl with rfl | ⟨a,rfl⟩
  · obtain ⟨n,h⟩ := negative_hit M 1
    refine ⟨n,(ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
    have he : signed (-1) = 3 := by decide
    simpa [he] using h
  · obtain ⟨n,h⟩ := negative_hit M (2*a+1+2)
    rw [signed_lower,show 2*a+1+1=2*(a+1) by omega,pow_mul] at h
    refine ⟨n,(ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
    simpa using h

private lemma opposite_excluded {m n : ℕ} (h : lucasFibonacciSum n ≡ lowerNeighborAtAddTwo (2*m) [MOD 11]) :
    False := by
  obtain ⟨j,hj⟩ := negative_hit 11 (2*m+2)
  rw [signed_lower,pow_succ,pow_mul] at hj
  have he := (ZMod.natCast_eq_natCast_iff ..).mpr h
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hjneg : (lucasFibonacciSum j : ZMod 11) = -(lucasFibonacciSum n : ZMod 11) := by
    simpa [he] using hj
  have hs (a : ℕ) : (lucasFibonacciSum a : ZMod 11) = (2^a)^2 := by
    rw [upper_mod_eleven,←pow_mul, mul_comm, pow_mul]
    norm_num
  have bad : ∀ v w : ZMod 11, w ≠ 0 → v^2 ≠ -w^2 := by decide
  apply bad (2^j) (2^n) (pow_ne_zero _ (by decide))
  simpa only [←hs] using hjneg

private lemma orientation {y n : ℕ} (h : lucasFibonacciSum n ≡ y [MOD 11])
    (hu : (∃ j, y = lucasFibonacciSum j) ∨ IsLowerNeighborValue y) :
    (∃ j, y = lucasFibonacciSum j) ∨ OddLowerValue y := by
  rcases hu with hu | rfl | ⟨m,rfl⟩
  · exact Or.inl hu
  · exact Or.inr (Or.inl rfl)
  · rcases Nat.even_or_odd m with ⟨a,ha⟩ | ⟨a,ha⟩
    · rw [show m=2*a by omega] at h
      exact (opposite_excluded h).elim
    · exact Or.inr (Or.inr ⟨a,by rw [show m=2*a+1 by omega]⟩)

private lemma detected_values {y n : ℕ} (h : lucasFibonacciSum n ≡ y [MOD testModulus y]) :
    (∃ j, y = lucasFibonacciSum j) ∨ OddLowerValue y := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_cases hy : y < 3
  · rw [testModulus, if_pos hy] at h
    have he := (ZMod.natCast_eq_natCast_iff ..).mpr h
    rw [upper_mod_eleven] at he
    interval_cases y
    · exact (pow_ne_zero _ (by decide : (4 : ZMod 11) ≠ 0) (by simpa using he)).elim
    · exact Or.inl ⟨0,rfl⟩
    · have bad : ∀ w : ZMod 11, w^2 ≠ 2 := by decide
      apply (bad (2^n) ?_).elim
      rwa [←pow_mul,mul_comm,pow_mul,show (2:ZMod 11)^2=4 by decide]
  let A := 5*y^2+44
  let B := 5*y^2-44
  have hm : testModulus y = 11*(A^2*B^2) := if_neg hy
  have hB := minus_pos (y := y) (by omega)
  apply orientation (h.of_dvd (show 11 ∣ testModulus y from ⟨_,hm⟩))
  apply (either_diagonal_iff_pell y).mpr
  obtain ⟨x,hx|hx⟩ := (either_diagonal_iff_pell (lucasFibonacciSum n)).mp (Or.inl ⟨n,rfl⟩)
  · have ha := h.of_dvd (show A^2 ∣ testModulus y by rw [hm]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    obtain ⟨v,hv⟩ := square_of_mod_self_sq (D := A) (by dsimp [A]; omega)
      (x := x) (by rw [hx]; exact ((ha.pow 2).mul_left 5).add_right 44)
    exact ⟨v,Or.inl hv⟩
  · have hb := h.of_dvd (show B^2 ∣ testModulus y by rw [hm]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
    have eqB : B+44=5*y^2 := Nat.sub_add_cancel hB.le
    have hh : x^2+44 ≡ B+44 [MOD B^2] := by
      rw [hx,eqB]
      exact (hb.pow 2).mul_left 5
    obtain ⟨v,hv⟩ := square_of_mod_self_sq (by dsimp [B]; omega) (hh.add_right_cancel' 44)
    exact ⟨v,Or.inr (by omega)⟩

/-- Exactly the upper values and odd-index lower values survive all congruence tests. -/
theorem upper_modular_closure (y : ℕ) :
    (∀ M > 0, ∃ n, lucasFibonacciSum n ≡ y [MOD M]) ↔
      (∃ j, y = lucasFibonacciSum j) ∨ OddLowerValue y := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h (testModulus y) (modulus_pos y)
    exact detected_values hn
  · rintro (⟨j,rfl⟩ | hl) M hM
    · exact ⟨j,Nat.ModEq.refl _⟩
    · let : NeZero M := ⟨hM.ne'⟩
      exact odd_lower_hit hl M

/-- A hit modulo eleven distinguishes the admissible orientation inside the two diagonals. -/
theorem closure_of_eleven_and_diagonal {y : ℕ} (h11 : ∃ n, lucasFibonacciSum n ≡ y [MOD 11])
    (h : (∃ j, y = lucasFibonacciSum j) ∨ IsLowerNeighborValue y) :
    ∀ M > 0, ∃ n, lucasFibonacciSum n ≡ y [MOD M] := by
  obtain ⟨n,hn⟩ := h11
  exact (upper_modular_closure y).mpr (orientation hn h)

/-- A single bounded orbit test decides membership in the all-moduli closure. -/
theorem upper_modular_closure_finite_test (y : ℕ) :
    (∀ M > 0, ∃ n, lucasFibonacciSum n ≡ y [MOD M]) ↔
      ∃ n < (testModulus y)^2, lucasFibonacciSum n ≡ y [MOD testModulus y] := by
  have hM := modulus_pos y
  let : NeZero (testModulus y) := ⟨hM.ne'⟩
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h _ hM
    exact bounded_hit hn
  · rintro ⟨n,_,hn⟩
    exact (upper_modular_closure y).mpr (detected_values hn)

/-- The surplus over actual upper values consists of the odd lower values other than five. -/
theorem upper_false_positives (y : ℕ) :
    ((∀ M > 0, ∃ n, lucasFibonacciSum n ≡ y [MOD M]) ∧ ¬ ∃ n, y = lucasFibonacciSum n) ↔
      OddLowerValue y ∧ y ≠ 5 := by
  rw [upper_modular_closure]
  have hl : OddLowerValue y → IsLowerNeighborValue y := by
    rintro (rfl | ⟨a,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_,rfl⟩
  constructor
  · rintro ⟨hu|ho,hn⟩
    · exact (hn hu).elim
    · exact ⟨ho,fun h => hn (((both_diagonals_iff_five y).mpr h).1)⟩
  · rintro ⟨ho,h5⟩
    exact ⟨Or.inr ho,fun hu => h5 ((both_diagonals_iff_five y).mp ⟨hu,hl ho⟩)⟩

/-- The primes three and 31 illustrate the congruence obstruction at every modulus. -/
theorem false_positive_primes : ∀ p ∈ ({3,31} : Finset ℕ), p.Prime ∧
    (∀ M > 0, ∃ n, lucasFibonacciSum n ≡ p [MOD M]) ∧ ¬ ∃ n, p = lucasFibonacciSum n := by
  intro p hp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨by decide,(upper_false_positives 3).mpr ⟨Or.inl rfl,by decide⟩⟩
  · exact ⟨by decide,(upper_false_positives 31).mpr ⟨Or.inr ⟨2,by decide⟩,by decide⟩⟩

#print axioms signed_nat
#print axioms signed_lower
#print axioms upper_mod_eleven
#print axioms signed_fifth
#print axioms signed_progression_hit
#print axioms square_of_mod_self_sq
#print axioms upper_modular_closure
#print axioms closure_of_eleven_and_diagonal
#print axioms upper_modular_closure_finite_test
#print axioms upper_false_positives
#print axioms false_positive_primes

end CongruenceClosure
end Arxiv.«2211.10788»
