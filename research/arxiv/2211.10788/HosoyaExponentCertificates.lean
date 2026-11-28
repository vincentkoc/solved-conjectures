import HosoyaAuxiliaryPrime

/-! Split-prime restrictions on perfect powers along the Fibonacci subsequence F₆ₜ. -/

namespace Arxiv.«2211.10788».HosoyaAuxiliaryPrime

open RealEleven

private theorem fib_six_cycle {q T : ℕ}
    (h₀ : (Nat.fastFib (6*T) : ZMod q)=0)
    (h₁ : (Nat.fastFib (6*T+1) : ZMod q)=1) (t : ℕ) :
    (Nat.fib (6*t) : ZMod q)=Nat.fastFib (6*(t%T)) := by
  simp only [Nat.fastFib_eq] at *
  have shift (n : ℕ) : (Nat.fib (n+6*T) : ZMod q)=Nat.fib n := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using h₀
    | one => simpa [add_comm] using h₁
    | more n h₀ h₁ =>
      rw [show n+2+6*T=n+6*T+2 by omega,Nat.fib_add_two (n:=n+6*T),Nat.fib_add_two (n:=n)]
      push_cast
      rw [h₀, show n+6*T+1=n+1+6*T by omega, h₁]
  by_cases hT : T=0
  · simp [hT]
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t<T
    · rw [Nat.mod_eq_of_lt ht]
    let u := t-T
    have he : t=u+T := by dsimp [u]; omega
    have hu : u<t := by dsimp [u]; omega
    rw [he,Nat.mul_add,shift,Nat.add_mod_right]
    exact ih u hu

/-- At this split prime, the two lists record allowed k-th powers of the
nonzero reductions of 1+f√11 and its conjugate. -/
structure SplitRow where
  q : ℕ
  T : ℕ
  r : ℕ
  k : ℕ
  plus : List ℕ
  minus : List ℕ
  prime : q.Prime
deriving DecidableEq

private lemma binary_pow {q : ℕ} (a : ZMod q) (n : ℕ) : npowBinRec n a = a^n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

private def SplitRow.orbitAt (s : SplitRow) (f : ZMod s.q) : Prop :=
  let x := 1+f*s.r
  let z := 1-f*s.r
  (x≠0 ∧ (npowBinRec s.k x).val ∈ s.plus) ∨ (z≠0 ∧ (npowBinRec s.k z).val ∈ s.minus) ∨
    (x≠0 ∧ z≠0 ∧ npowBinRec s.k (x*z) ≠ 1)

private instance (s : SplitRow) (f : ZMod s.q) : Decidable (s.orbitAt f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The Fibonacci state returns after T steps and every intervening residue passes the row. -/
def SplitRow.Valid (s : SplitRow) (p : ℕ) : Prop :=
  p*s.k=s.q-1 ∧ 0<s.T ∧
  (s.r:ZMod s.q)*s.r=11 ∧ (Nat.fastFib (6*s.T):ZMod s.q)=0 ∧
  (Nat.fastFib (6*s.T+1):ZMod s.q)=1 ∧
  ∀ j : Fin s.T, s.orbitAt (Nat.fastFib (6*j.val))

instance (s : SplitRow) (p : ℕ) : Decidable (s.Valid p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Both choices of the square root use the same global unit exponent. -/
def SplitRow.Allows (s : SplitRow) (i : ℕ) : Prop :=
  (npowBinRec i (npowBinRec s.k (10+3*(s.r:ZMod s.q)))).val ∈ s.plus ∨
  (npowBinRec i (npowBinRec s.k (10-3*(s.r:ZMod s.q)))).val ∈ s.minus

instance (s : SplitRow) (i : ℕ) : Decidable (s.Allows i) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem SplitRow.allows_of_twist {s : SplitRow} {p t i : ℕ} (h : s.Valid p)
    {v : RingEleven}
    (hv : (⟨1,Nat.fib (6*t)⟩ : RingEleven) = (baseUnit:RingEleven)^i*v^p) :
    s.Allows i := by
  obtain ⟨hk,hT,hr,h₀,h₁,ht⟩ := h
  let : Fact s.q.Prime := ⟨s.prime⟩
  have hc := compatible_of_twist hk hr hv
  simp only [Int.cast_natCast] at hc
  have hm := ht ⟨t%s.T,Nat.mod_lt _ hT⟩
  change s.orbitAt (Nat.fastFib (6*(t%s.T))) at hm
  rw [←fib_six_cycle h₀ h₁ t] at hm
  simp only [SplitRow.orbitAt,binary_pow] at hm
  simp only [SplitRow.Allows,binary_pow]
  obtain ⟨hx,hz⟩ := hc
  rcases hm with ⟨nx,mem⟩ | ⟨nz,mem⟩ | ⟨nx,nz,ne⟩
  · exact Or.inl ((hx.resolve_left nx) ▸ mem)
  · exact Or.inr ((hz.resolve_left nz) ▸ mem)
  · exfalso
    apply ne
    rw [mul_pow,hx.resolve_left nx,hz.resolve_left nz,←mul_pow,←mul_pow]
    have he : (10+3*(s.r:ZMod s.q))*(10-3*s.r)=1 := by linear_combination -9*hr
    simp [he]

/-- Across all the split primes, the same unit exponent must survive. -/
theorem fib_power_excluded_of_rows {p n : ℕ} (hp : Odd p) (hp₁ : 1 < p)
    (rows : List SplitRow) (valid : ∀ s ∈ rows, s.Valid p)
    (cover : ∀ i : Fin p, (∀ s ∈ rows, s.Allows i.val) → i.val=0)
    (hn : 0 < n) (hd : 6 ∣ n) (y : ℤ) : y^p+1 ≠ 11*(Nat.fib n:ℤ)^2 := by
  intro he
  obtain ⟨t,rfl⟩ := hd
  have hf := (by decide : 2 ∣ Nat.fib 6).trans (Nat.fib_dvd 6 (6*t) (dvd_mul_right ..))
  obtain ⟨i,v,hv⟩ := odd_norm_unit_twists hp (by exact_mod_cast hf) he
  have hi := cover i (fun s hs => SplitRow.allows_of_twist (valid s hs) hv)
  rw [hi,pow_zero,one_mul] at hv
  have hz := pure_power hp hp₁ hv
  have hpos := Nat.fib_pos.mpr hn
  omega

#print axioms fib_power_excluded_of_rows

end Arxiv.«2211.10788».HosoyaAuxiliaryPrime
