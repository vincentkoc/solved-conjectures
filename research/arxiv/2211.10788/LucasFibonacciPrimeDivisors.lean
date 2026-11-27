import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes

/-! Prime divisors of composite terms on the third diagonal of the determinant Hosoya triangle.
The definition agrees with Ching, Flórez, Luca, Mukherjee and Saunders, arXiv:2211.10788,
as formalized in `FormalConjectures/Arxiv/2211.10788/LucasFibonacciSumPrimes.lean`. -/

namespace Arxiv.«2211.10788»

private theorem sum_strictMono : StrictMono lucasFibonacciSum := by
  intro a b hab
  exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono hab.le))
    (Nat.fib_add_two_strictMono hab)

/-- The Fibonacci pair returns to its initial residue along an arithmetic progression. -/
private theorem exists_return (m s d : ℕ) [NeZero m] :
    ∃ t > 0, lucasFibonacciSum (s + d * t) ≡ lucasFibonacciSum s [MOD m] := by
  let state (n : ℕ) : ZMod m × ZMod m := (Nat.fib n, Nat.fib (n + 1))
  let step (v : ZMod m × ZMod m) := (v.2, v.1 + v.2)
  have hstep : Function.Injective step := by
    rintro ⟨a, b⟩ ⟨c, e⟩ he
    change (b, a + b) = (e, c + e) at he
    obtain ⟨rfl, h⟩ := Prod.mk.inj he
    exact Prod.ext (add_right_cancel h) rfl
  have hs : Function.Semiconj state Nat.succ step := by
    intro n
    exact Prod.ext rfl (by simp [state, step, Nat.fib_add_two])
  obtain ⟨t, ht, hfix⟩ := hstep.mem_periodicPts (state s)
  refine ⟨t, ht, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  have he := (hs.iterate_right (d * t) s).trans (hfix.const_mul d).eq
  rw [Nat.succ_iterate] at he
  simpa only [state, lucasFibonacciSum, Nat.fib_add_two, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat] using congrArg (fun v : ZMod m × ZMod m => 2 * v.1 + (v.1 + v.2)) he

/-- In every arithmetic progression of nonzero step, the composite terms have infinitely
many distinct prime divisors. -/
theorem infinite_prime_divisors_of_composite_lucasFibonacciSum (r d : ℕ) (hd : 0 < d) :
    {p : ℕ | p.Prime ∧ ∃ k : ℕ,
      ¬ (lucasFibonacciSum (r + d * k)).Prime ∧ p ∣ lucasFibonacciSum (r + d * k)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  let s := r + d
  let a := lucasFibonacciSum s
  have ha : 1 < a := sum_strictMono (show 0 < s by dsimp [s]; omega)
  have hmod : 0 < a * B.factorial := Nat.mul_pos (by omega) (Nat.factorial_pos _)
  let : NeZero (a * B.factorial) := ⟨hmod.ne'⟩
  obtain ⟨t, ht, hret⟩ := exists_return (a * B.factorial) s d
  have hgrow : a < lucasFibonacciSum (s + d * t) :=
    sum_strictMono (Nat.lt_add_of_pos_right (Nat.mul_pos hd ht))
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_exists_eq_add hgrow.le).mp hret.symm
  have hfactor : lucasFibonacciSum (s + d * t) = a * (B.factorial * j + 1) := by
    rw [hj]
    ring
  have hjpos : 0 < j := by
    by_contra! h
    have : j = 0 := by omega
    simp [this] at hj
    exact hgrow.ne' hj
  have hq : 1 < B.factorial * j + 1 := by
    have := Nat.mul_pos (Nat.factorial_pos B) hjpos
    omega
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq.ne'
  refine ⟨p, ⟨hp, t + 1, ?_⟩, ?_⟩
  · rw [show r + d * (t + 1) = s + d * t by dsimp [s]; ring, hfactor]
    exact ⟨Nat.not_prime_mul ha.ne' hq.ne', hpq.trans (dvd_mul_left _ _)⟩
  · by_contra! hpB
    have hpd := dvd_mul_of_dvd_left (Nat.dvd_factorial hp.pos hpB) j
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpd).mpr hpq)

#print axioms infinite_prime_divisors_of_composite_lucasFibonacciSum

end Arxiv.«2211.10788»
