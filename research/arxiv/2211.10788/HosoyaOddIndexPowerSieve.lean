import Mathlib

/-! Finite-field obstructions to odd prime powers on the odd Hosoya diagonals. -/

namespace Arxiv.«2211.10788».OddIndexPowers

/-- At physical index n these are the two neighbors, in Fibonacci coordinates.
The lower expression extends to the signed value −1 at index zero. -/
def value (lower : Bool) (n : ℕ) : ℤ :=
  if lower then 4*(Nat.fib n : ℤ)-Nat.fib (n+1) else 3*(Nat.fib n : ℤ)+Nat.fib (n+1)

private def pair (q n : ℕ) : ZMod q × ZMod q :=
  ((Nat.fastFibAux n).1, (Nat.fastFibAux n).2)

private theorem pair_period {q T : ℕ} (h : pair q T = (0,1)) (n : ℕ) :
    pair q n = pair q (n%T) := by
  let step (v : ZMod q × ZMod q) := (v.2, v.1+v.2)
  have next (i : ℕ) : pair q (i+1) = step (pair q i) := by
    simp [pair, step, Nat.fastFibAux_eq, Nat.fib_add_two]
  have per : Function.Periodic (pair q) T := by
    intro i
    induction i with
    | zero => simpa [pair, Nat.fastFibAux_eq] using h
    | succ i ih =>
      rw [show i+1+T=i+T+1 by omega, next, next i, ih]
  have eq := per.nat_mul (n/T) (n%T)
  change pair q (n%T + (n/T)*T) = pair q (n%T) at eq
  rwa [Nat.mul_comm (n/T) T, Nat.mod_add_div] at eq

private def ev (lower : Bool) {q : ℕ} (v : ZMod q × ZMod q) : ZMod q :=
  if lower then 4*v.1-v.2 else 3*v.1+v.2

private theorem cast_value (lower : Bool) (q n : ℕ) : (value lower n : ZMod q) = ev lower (pair q n) := by
  cases lower <;> simp [value, ev, pair, Nat.fastFibAux_eq]

private theorem bin_pow {q : ℕ} (x : ZMod q) (k : ℕ) : npowBinRec k x = x^k := by
  induction k with
  | zero => simp [npowBinRec_zero]
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

private structure Row where
  q : ℕ
  period : ℕ
  projection : ℕ
  character : ℕ
  residues : List ℕ
  prime : q.Prime
deriving DecidableEq

/-- The lower diagonal at odd indices corresponds to negative upper indices.
Both finite-field implications are checked directly on the Fibonacci cycle. -/
private def Row.allows (s : Row) (lower : Bool) (n : ℕ) : Bool :=
  let a := n % s.projection
  s.residues.contains (if lower then (s.projection-a)%s.projection else a)

private def Row.valid (s : Row) (p : ℕ) : Prop :=
  p*s.character = s.q-1 ∧ 0 < s.period ∧ 2 ∣ s.period ∧
  s.projection ∣ s.period ∧ s.projection ∣ 2*p ∧ pair s.q s.period = (0,1) ∧
  ∀ i : Fin s.period, i.val%2 = 1 → ∀ lower : Bool,
    let x := ev lower (pair s.q i.val)
    (x = 0 ∨ npowBinRec s.character x = 1) → s.allows lower i.val = true

private instance (s : Row) (p : ℕ) : Decidable (s.valid p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem Row.sound {s : Row} {p n : ℕ} (h : s.valid p) (lower : Bool)
    (hn : n%2 = 1) {y : ℤ} (hy : value lower n = y^p) : s.allows lower (n%(2*p)) = true := by
  obtain ⟨hk, hT, htwo, hdiv, hp, hper, htest⟩ := h
  let : Fact s.q.Prime := ⟨s.prime⟩
  have hc : ev lower (pair s.q n) = (y : ZMod s.q)^p := by
    rw [← cast_value, hy, Int.cast_pow]
  have powtest : ev lower (pair s.q n) = 0 ∨ npowBinRec s.character (ev lower (pair s.q n)) = 1 := by
    rw [hc, bin_pow, ← pow_mul, hk]
    by_cases hz : (y : ZMod s.q) = 0
    · left
      have hp' : p ≠ 0 := by have := s.prime.one_lt; intro hz'; simp [hz'] at hk; omega
      simp [hz, hp']
    · exact Or.inr (ZMod.pow_card_sub_one_eq_one hz)
  rw [pair_period hper n] at powtest
  have hi : (n%s.period)%2=1 := (Nat.mod_mod_of_dvd n htwo).trans hn
  have pass := htest ⟨n%s.period, Nat.mod_lt n hT⟩ hi lower powtest
  change s.allows lower (n%s.period) = true at pass
  simpa only [Row.allows, Nat.mod_mod_of_dvd n hdiv, Nat.mod_mod_of_dvd n hp] using pass

private def rows : ℕ → List Row
  | 3 => [⟨7, 16, 2, 2, [], by norm_num⟩]
  | 5 => [⟨11, 10, 10, 2, [5], by norm_num⟩,
      ⟨31, 30, 10, 6, [3, 7, 9], by norm_num⟩]
  | 7 => [⟨29, 14, 14, 4, [9], by norm_num⟩,
      ⟨211, 42, 14, 30, [1, 3, 5, 13], by norm_num⟩]
  | 11 => [⟨199, 22, 22, 18, [], by norm_num⟩]
  | 13 => [⟨911, 70, 2, 70, [], by norm_num⟩]
  | 17 => [⟨3571, 34, 34, 210, [], by norm_num⟩]
  | 19 => [⟨9349, 38, 38, 492, [], by norm_num⟩]
  | 23 => [⟨47, 32, 2, 2, [], by norm_num⟩]
  | 29 => [⟨1103, 96, 2, 38, [], by norm_num⟩]
  | 31 => [⟨1427, 168, 2, 46, [], by norm_num⟩]
  | 37 => [⟨2221, 148, 74, 60, [37], by norm_num⟩,
      ⟨4441, 222, 74, 120, [11, 35], by norm_num⟩]
  | 41 => [⟨9349, 38, 2, 228, [], by norm_num⟩]
  | 43 => [⟨6709, 86, 86, 156, [], by norm_num⟩]
  | 47 => [⟨5641, 376, 94, 120, [25, 31, 57, 61], by norm_num⟩,
      ⟨941, 470, 94, 20, [3, 5, 17, 41, 49, 91], by norm_num⟩]
  | 53 => [⟨107, 72, 2, 2, [], by norm_num⟩]
  | 59 => [⟨709, 118, 118, 12, [53], by norm_num⟩,
      ⟨8969, 118, 118, 152, [45, 55], by norm_num⟩]
  | 61 => [⟨86011, 610, 122, 1410, [61, 83], by norm_num⟩,
      ⟨1709, 854, 122, 28, [1, 5, 23, 81, 99, 103], by norm_num⟩]
  | 67 => [⟨4021, 134, 134, 60, [], by norm_num⟩]
  | 71 => [⟨1279, 426, 142, 18, [23], by norm_num⟩,
      ⟨569, 568, 142, 8, [41], by norm_num⟩]
  | 73 => [⟨41611, 190, 2, 570, [], by norm_num⟩]
  | 79 => [⟨12641, 790, 158, 160, [75, 95], by norm_num⟩,
      ⟨2371, 790, 158, 30, [11, 45, 109, 121, 129], by norm_num⟩]
  | 83 => [⟨5147, 1144, 2, 62, [], by norm_num⟩]
  | 89 => [⟨39161, 110, 2, 440, [], by norm_num⟩]
  | 97 => [⟨3299, 194, 194, 34, [], by norm_num⟩]
  | _ => []

private def Certificate (p : ℕ) : Prop :=
  (∀ s ∈ rows p, s.valid p) ∧
  ∀ i : Fin (2*p), i.val%2=1 → ∀ lower : Bool, ∃ s ∈ rows p, s.allows lower i.val = false

private instance (p : ℕ) : Decidable (Certificate p) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem certificates : ∀ p : Fin 101, p.val.Prime → 3 ≤ p.val → Certificate p.val := by
  decide +kernel

/-- At every odd physical index neither neighbor is a pth power for any odd
prime p below 101. This is a statement about entire individual terms. -/
theorem odd_index_not_small_prime_power (lower : Bool) {p n : ℕ}
    (hp : p.Prime) (hp₃ : 3 ≤ p) (hp₁₀₁ : p < 101) (hn : Odd n) (y : ℤ) :
    value lower n ≠ y^p := by
  intro he
  obtain ⟨valid, cover⟩ := certificates ⟨p,hp₁₀₁⟩ hp hp₃
  have hn' := Nat.odd_iff.mp hn
  have hi : (n%(2*p))%2=1 := (Nat.mod_mod_of_dvd n (dvd_mul_right 2 p)).trans hn'
  obtain ⟨s, hs, hbad⟩ := cover ⟨n%(2*p), Nat.mod_lt _ (by omega)⟩ hi lower
  exact Bool.noConfusion ((Row.sound (valid s hs) lower hn' he).symm.trans hbad)

#print axioms odd_index_not_small_prime_power

end Arxiv.«2211.10788».OddIndexPowers
