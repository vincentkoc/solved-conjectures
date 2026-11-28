import FormalConjectures.Arxiv.«2211.10788».LucasFibonacciSumPrimes
import research.arxiv.«2211.10788».LucasFibonacciProgressionDivisors

/-! Lifting a Lucas–Fibonacci divisor along a progression to one higher prime power. -/

namespace Arxiv.«2211.10788»

/-- Constant coefficient of the jth power of a root of X² − X − 1. -/
def fibonacciStepConstant : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.fib j

private lemma constant_add_two (j : ℕ) :
    fibonacciStepConstant (j + 2) = fibonacciStepConstant j + fibonacciStepConstant (j + 1) := by
  cases j with
  | zero => decide
  | succ j => exact Nat.fib_add_two

private lemma sequence_shift (v : ℕ → ℕ) (hv : ∀ n, v (n + 2) = v (n + 1) + v n) (s j : ℕ) :
    v (s + j) = fibonacciStepConstant j * v s + Nat.fib j * v (s + 1) := by
  induction j using Nat.twoStepInduction with
  | zero => simp [fibonacciStepConstant]
  | one => simp [fibonacciStepConstant]
  | more j h0 h1 =>
    rw [← Nat.add_assoc, hv, Nat.add_assoc s j 1, h1, h0,
      constant_add_two, Nat.fib_add_two]
    ring

private lemma step_coprime (j : ℕ) : (Nat.fib j).Coprime (fibonacciStepConstant j) := by
  cases j with
  | zero => decide
  | succ j => exact (Nat.fib_coprime_fib_succ j).symm

private lemma consecutive_coprime (s : ℕ) :
    (lucasFibonacciSum s).Coprime (lucasFibonacciSum (s + 1)) := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [lucas_fibonacci_sum_recurrence]
    simpa using ih.symm

private lemma lifted_quotient (v : ℕ → ℕ) (hv : ∀ n, v (n + 2) = v (n + 1) + v n)
    {m s j : ℕ} (hm : 0 < m) (hs : m ∣ v s)
    (hf : m ∣ Nat.fib j) (t : ℕ) :
    m ∣ v (s + j * t) ∧
      v (s + j * (t + 1)) / m =
        fibonacciStepConstant j * (v (s + j * t) / m) +
        (Nat.fib j / m) * v (s + j * t + 1) := by
  have hall (u : ℕ) : m ∣ v (s + j * u) := by
    induction u with
    | zero => simpa using hs
    | succ u ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, sequence_shift v hv (s + j * u) j]
      exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_of_dvd_left hf _)
  refine ⟨hall t, Nat.mul_right_cancel hm ?_⟩
  rw [Nat.div_mul_cancel (hall (t + 1)), Nat.add_mul]
  calc
    v (s + j * (t + 1)) =
        fibonacciStepConstant j * v (s + j * t) + Nat.fib j * v (s + j * t + 1) := by
      rw [Nat.mul_succ, ← Nat.add_assoc, sequence_shift v hv (s + j * t) j]
    _ = _ := by
      rw [Nat.mul_assoc, Nat.div_mul_cancel (hall t)]
      rw [mul_right_comm (Nat.fib j / m), Nat.div_mul_cancel hf]

private lemma normalized_shift (v : ℕ → ℕ) (hv : ∀ n, v (n + 2) = v (n + 1) + v n)
    {p m s j : ℕ} (hm : 0 < m) (hpm : p ∣ m) (hs : m ∣ v s)
    (hf : m ∣ Nat.fib j) (t : ℕ) :
    (fibonacciStepConstant j : ZMod p) * ((v (s + j * t) / m : ℕ) : ZMod p) =
      (fibonacciStepConstant j : ZMod p) ^ t * (fibonacciStepConstant j * ((v s / m : ℕ) : ZMod p) +
      t * ((Nat.fib j / m : ℕ) : ZMod p) * v (s + 1)) := by
  let A : ZMod p := fibonacciStepConstant j
  let B : ZMod p := ((Nat.fib j / m : ℕ) : ZMod p)
  let X (u : ℕ) : ZMod p := ((v (s + j * u) / m : ℕ) : ZMod p)
  let Y (u : ℕ) : ZMod p := v (s + j * u + 1)
  have hpf : p ∣ Nat.fib j := hpm.trans hf
  have hy (u : ℕ) : Y (u + 1) = A * Y u := by
    dsimp only [Y, A]
    rw [show s + j * (u + 1) + 1 = (s + j * u + 1) + j by ring, sequence_shift v hv (s + j * u + 1) j]
    push_cast
    rw [(ZMod.natCast_eq_zero_iff ..).mpr hpf]
    ring
  have hyr (u : ℕ) : Y u = A ^ u * Y 0 := by
    induction u with
    | zero => simp
    | succ u ih => rw [hy, ih, pow_succ]; ring
  have hx (u : ℕ) : X (u + 1) = A * X u + B * Y u := by
    simpa only [X, A, B, Y, Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : ZMod p)) (lifted_quotient v hv hm hs hf u).2
  have hlin (u : ℕ) : A * X u = A ^ u * (A * X 0 + u * B * Y 0) := by
    induction u with
    | zero => simp
    | succ u ih =>
      rw [hx, hyr, pow_succ, Nat.cast_succ]
      linear_combination A * ih
  simpa [A, B, X, Y] using hlin t

private lemma affine_lift (v : ℕ → ℕ) (hv : ∀ n, v (n + 2) = v (n + 1) + v n)
    {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m) (hpm : p ∣ m) (hs : m ∣ v s)
    (hf : m ∣ Nat.fib j) (t : ℕ) :
    p * m ∣ v (s + j * t) ↔
      (fibonacciStepConstant j : ZMod p) * ((v s / m : ℕ) : ZMod p) +
      t * ((Nat.fib j / m : ℕ) : ZMod p) * v (s + 1) = 0 := by
  let A : ZMod p := fibonacciStepConstant j
  let B : ZMod p := ((Nat.fib j / m : ℕ) : ZMod p)
  let X (u : ℕ) : ZMod p := ((v (s + j * u) / m : ℕ) : ZMod p)
  let Y (u : ℕ) : ZMod p := v (s + j * u + 1)
  have hpf : p ∣ Nat.fib j := hpm.trans hf
  have ha : A ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr (fun hd =>
    (Fact.out : p.Prime).not_dvd_one ((step_coprime j).gcd_eq_one ▸ Nat.dvd_gcd hpf hd))
  have ht : A * X t = A ^ t * (A * X 0 + t * B * Y 0) := by
    simpa [A, B, X, Y] using normalized_shift (p := p) v hv hm hpm hs hf t
  have hdiv := (lifted_quotient v hv hm hs hf t).1
  have hcancel : p * m ∣ v (s + j * t) ↔ p ∣ v (s + j * t) / m := by
    conv_lhs => rw [← Nat.div_mul_cancel hdiv]
    exact Nat.mul_dvd_mul_iff_right hm
  rw [hcancel, ← ZMod.natCast_eq_zero_iff]
  change X t = 0 ↔ _
  calc
    X t = 0 ↔ A * X t = 0 := by simp [ha]
    _ ↔ A ^ t * (A * X 0 + t * B * Y 0) = 0 := by rw [ht]
    _ ↔ _ := by simp [ha, A, X, B, Y]

/-- Once m divides the term and the Fibonacci step, divisibility by p * m
on the same progression is equivalent to a single affine congruence. -/
theorem prime_mul_dvd_lucasFibonacciSum_iff {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m)
    (hpm : p ∣ m) (hs : m ∣ lucasFibonacciSum s) (hf : m ∣ Nat.fib j) (t : ℕ) :
    p * m ∣ lucasFibonacciSum (s + j * t) ↔
      (fibonacciStepConstant j : ZMod p) * ((lucasFibonacciSum s / m : ℕ) : ZMod p) +
      t * ((Nat.fib j / m : ℕ) : ZMod p) * lucasFibonacciSum (s + 1) = 0 :=
  affine_lift lucasFibonacciSum lucas_fibonacci_sum_recurrence hm hpm hs hf t

private lemma cast_quot_ne_zero_iff {p m a : ℕ} (hm : 0 < m) (ha : m ∣ a) :
    (((a / m : ℕ) : ZMod p) ≠ 0) ↔ ¬p * m ∣ a := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  conv_rhs => rw [← Nat.div_mul_cancel ha]
  rw [Nat.mul_dvd_mul_iff_right hm]

private theorem recurrence_lifts_on_class (v : ℕ → ℕ)
    (step : ∀ n, v (n+2) = v (n+1)+v n) (cop : ∀ n, (v n).Coprime (v (n+1))) {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m)
    (hpm : p ∣ m) (hs : m ∣ v s) (hf : m ∣ Nat.fib j) :
    (if p * m ∣ Nat.fib j then
      ∀ t : ℕ, p * m ∣ v (s + j * t) ↔ p * m ∣ v s
     else
      ∃! z : ZMod p, ∀ t : ℕ, p * m ∣ v (s + j * t) ↔ (t : ZMod p) = z) := by
  let a : ZMod p := fibonacciStepConstant j
  let x : ZMod p := ((v s / m : ℕ) : ZMod p)
  let b : ZMod p := ((Nat.fib j / m : ℕ) : ZMod p)
  let y : ZMod p := v (s + 1)
  have ha : a ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr (fun hd =>
    (Fact.out : p.Prime).not_dvd_one ((step_coprime j).gcd_eq_one ▸ Nat.dvd_gcd (hpm.trans hf) hd))
  have hy : y ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr (fun hd =>
    (Fact.out : p.Prime).not_dvd_one ((cop s).gcd_eq_one ▸ Nat.dvd_gcd (hpm.trans hs) hd))
  have htest (t : ℕ) : p * m ∣ v (s + j * t) ↔ a * x + t * b * y = 0 :=
    affine_lift v step hm hpm hs hf t
  split_ifs with hstep
  · have hb : b = 0 := by
      by_contra hn
      exact ((cast_quot_ne_zero_iff hm hf).mp hn) hstep
    intro t
    rw [htest, hb]
    simp only [mul_zero, zero_mul, add_zero, mul_eq_zero, or_iff_right ha]
    exact not_iff_not.mp (cast_quot_ne_zero_iff hm hs)
  · have hb : b ≠ 0 := (cast_quot_ne_zero_iff hm hf).mpr hstep
    let z := -(a * x) / (b * y)
    have hz (t : ℕ) : p * m ∣ v (s + j * t) ↔ (t : ZMod p) = z := by
      rw [htest, eq_div_iff (mul_ne_zero hb hy)]
      constructor <;> intro h <;> linear_combination h
    refine ⟨z, hz, ?_⟩
    intro w hw
    obtain he := (hz w.val).mp ((hw w.val).mpr (ZMod.natCast_zmod_val w))
    simpa using he

/-- If the Fibonacci step gains the extra prime factor, every term or no term
lifts according to the initial value. Otherwise exactly one residue class of
steps lifts. The modulus may already be divisible by a higher power of p. -/
theorem prime_mul_lifts_on_class {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m)
    (hpm : p ∣ m) (hs : m ∣ lucasFibonacciSum s) (hf : m ∣ Nat.fib j) :
    (if p * m ∣ Nat.fib j then
      ∀ t : ℕ, p * m ∣ lucasFibonacciSum (s + j * t) ↔ p * m ∣ lucasFibonacciSum s
     else
      ∃! z : ZMod p, ∀ t : ℕ, p * m ∣ lucasFibonacciSum (s + j * t) ↔ (t : ZMod p) = z) :=
  recurrence_lifts_on_class _ lucas_fibonacci_sum_recurrence consecutive_coprime hm hpm hs hf

private lemma rank_spec (m d : ℕ) [NeZero m] :
    0 < fibonacciStepRank m d ∧ m ∣ Nat.fib (d * fibonacciStepRank m d) := by
  unfold fibonacciStepRank
  exact Nat.find_spec (p := fun t => 0 < t ∧ m ∣ Nat.fib (d * t)) _

private lemma rank_le {m d t : ℕ} [NeZero m] (ht : 0 < t) (h : m ∣ Nat.fib (d * t)) :
    fibonacciStepRank m d ≤ t := by
  unfold fibonacciStepRank
  exact Nat.find_min' _ ⟨ht,h⟩

private lemma rank_dvd_of_hit {m d t : ℕ} [NeZero m] (ht : m ∣ Nat.fib (d * t)) :
    fibonacciStepRank m d ∣ t := by
  let e := fibonacciStepRank m d
  obtain ⟨he,hv⟩ := rank_spec m d
  have hg : m ∣ Nat.fib (d * e.gcd t) := by
    rw [← Nat.gcd_mul_left, Nat.fib_gcd]
    exact Nat.dvd_gcd hv ht
  have heq : e = e.gcd t := le_antisymm (rank_le (Nat.gcd_pos_of_pos_left t he) hg)
    (Nat.le_of_dvd he (Nat.gcd_dvd_left ..))
  exact (dvd_of_eq heq).trans (Nat.gcd_dvd_right e t)

/-- At one higher prime-power level, the first Fibonacci return rank either
stays fixed or multiplies by p, including for nontrivial index steps. -/
theorem fibonacciStepRank_prime_mul {p m : ℕ} [Fact p.Prime] [NeZero m]
    (hpm : p ∣ m) (d : ℕ) :
    fibonacciStepRank (p * m) d = if p * m ∣ Nat.fib (d * fibonacciStepRank m d)
      then fibonacciStepRank m d else p * fibonacciStepRank m d := by
  let e := fibonacciStepRank m d
  let g := fibonacciStepRank (p * m) d
  have hm := NeZero.pos m
  obtain ⟨he,hf⟩ := rank_spec m d
  obtain ⟨hg,hG⟩ := rank_spec (p * m) d
  have hdiv : e ∣ g := rank_dvd_of_hit ((dvd_mul_left m p).trans hG)
  split_ifs with h
  · exact le_antisymm (rank_le he h) (Nat.le_of_dvd hg hdiv)
  have hb := (cast_quot_ne_zero_iff hm hf).mpr h
  have hit (u : ℕ) : p * m ∣ Nat.fib (d * (e * u)) ↔ p ∣ u := by
    have h := affine_lift Nat.fib (fun n => by rw [Nat.fib_add_two, add_comm]) (s := 0)
      hm hpm (by simp) hf u
    simpa [e, Nat.mul_assoc, Nat.fib_zero, hb, ← ZMod.natCast_eq_zero_iff u p] using h
  apply le_antisymm
  · calc g ≤ e * p := rank_le (Nat.mul_pos he (Fact.out : p.Prime).pos) ((hit p).mpr dvd_rfl)
         _ = p * e := Nat.mul_comm ..
  · obtain ⟨v,hv⟩ := hdiv
    have hpv := (hit v).mp (hv ▸ hG)
    have hvpos : 0 < v := by by_contra! hz; obtain rfl := Nat.eq_zero_of_le_zero hz; simp at hv; omega
    change p * e ≤ g
    rw [hv, Nat.mul_comm p e]
    exact Nat.mul_le_mul_left e (Nat.le_of_dvd hvpos hpv)

private lemma sharp_step_succ {p m j : ℕ} [Fact p.Prime] (hm : 0 < m) (hp2 : p * p ∣ m)
    (hf : m ∣ Nat.fib j) (hsharp : ¬p * m ∣ Nat.fib j) :
    p * m ∣ Nat.fib (j * p) ∧ ¬p * (p * m) ∣ Nat.fib (j * p) := by
  have hp : p.Prime := Fact.out
  have hpm : p ∣ m := (dvd_mul_right p p).trans hp2
  have hv (n : ℕ) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by rw [Nat.fib_add_two, add_comm]
  have h0 := affine_lift Nat.fib hv (s := 0) hm hpm (by simp) hf p
  refine ⟨by simpa using h0, ?_⟩
  intro hbad
  have hd := (lifted_quotient Nat.fib hv hm (s := 0) (by simp) hf p).1
  simp only [zero_add] at hd
  have hbad' : (p * p) * m ∣ Nat.fib (j * p) := by simpa [Nat.mul_assoc] using hbad
  have hz : p * p ∣ Nat.fib (j * p) / m := by
    apply (Nat.mul_dvd_mul_iff_right hm).mp
    rwa [Nat.div_mul_cancel hd]
  have hlin := normalized_shift (p := p * p) Nat.fib hv (s := 0) hm hp2 (by simp) hf p
  simp only [zero_add, Nat.fib_zero, Nat.zero_div, Nat.cast_zero, mul_zero, Nat.fib_one,
    Nat.cast_one, mul_one, (ZMod.natCast_eq_zero_iff ..).mpr hz] at hlin
  have hdiv : p * p ∣ p * ((fibonacciStepConstant j) ^ p * (Nat.fib j / m)) := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    push_cast
    linear_combination -hlin
  have hcancel := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdiv
  have ha : ¬p ∣ fibonacciStepConstant j := fun h =>
    hp.not_dvd_one ((step_coprime j).gcd_eq_one ▸ Nat.dvd_gcd (hpm.trans hf) h)
  rcases hp.dvd_mul.mp hcancel with ha' | hb'
  · exact ha (hp.dvd_of_dvd_pow ha')
  · apply hsharp
    have := mul_dvd_mul_right hb' m
    rwa [Nat.div_mul_cancel hf] at this

private lemma sharp_step_tower {p m j : ℕ} [Fact p.Prime] (hm : 0 < m) (hp2 : p * p ∣ m)
    (hf : m ∣ Nat.fib j) (hsharp : ¬p * m ∣ Nat.fib j) (b : ℕ) :
    p ^ b * m ∣ Nat.fib (j * p ^ b) ∧ ¬p * (p ^ b * m) ∣ Nat.fib (j * p ^ b) := by
  induction b with
  | zero => simpa using And.intro hf hsharp
  | succ b ih =>
    have hpos : 0 < p ^ b * m := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hm
    have hs := sharp_step_succ hpos (hp2.trans (dvd_mul_left m (p ^ b))) ih.1 ih.2
    simpa only [pow_succ' p b, Nat.mul_assoc, Nat.mul_right_comm j (p ^ b) p] using hs

private theorem recurrence_tower (v : ℕ → ℕ)
    (step : ∀ n, v (n+2) = v (n+1)+v n) (cop : ∀ n, (v n).Coprime (v (n+1))) {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m) (hp2 : p * p ∣ m)
    (hs : m ∣ v s) (hf : m ∣ Nat.fib j) (hsharp : ¬p * m ∣ Nat.fib j)
    (b : ℕ) : ∃ t < p ^ b, p ^ b * m ∣ v (s + j * t) := by
  induction b with
  | zero => exact ⟨0, by simp, by simpa using hs⟩
  | succ b ih =>
    obtain ⟨t,ht,hit⟩ := ih
    obtain ⟨hF,hn⟩ := sharp_step_tower hm hp2 hf hsharp b
    have hpm : p ∣ p ^ b * m := ((dvd_mul_right p p).trans hp2).trans (dvd_mul_left ..)
    have hl := recurrence_lifts_on_class v step cop (Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hm)
      hpm hit hF
    rw [if_neg hn] at hl
    obtain ⟨z,hz,_⟩ := hl
    refine ⟨t + p ^ b * z.val, ?_, ?_⟩
    · have := Nat.mul_le_mul_left (p ^ b) (Nat.succ_le_of_lt (ZMod.val_lt z))
      rw [Nat.mul_succ, ← pow_succ] at this
      omega
    · have h := (hz z.val).mpr (ZMod.natCast_zmod_val z)
      have hi : s + j * t + (j * p ^ b) * z.val = s + j * (t + p ^ b * z.val) := by ring
      rw [hi] at h
      simpa only [pow_succ', Nat.mul_assoc] using h

private lemma tower_of_hit {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m) (hp2 : p * p ∣ m)
    (hs : m ∣ lucasFibonacciSum s) (hf : m ∣ Nat.fib j) (hsharp : ¬p * m ∣ Nat.fib j)
    (b : ℕ) : ∃ t < p ^ b, p ^ b * m ∣ lucasFibonacciSum (s + j * t) :=
  recurrence_tower _ lucas_fibonacci_sum_recurrence consecutive_coprime hm hp2 hs hf hsharp b

/-- A root of a Fibonacci recurrence with coprime neighbors lifts along
a whole parameter class at every power of a sharp Fibonacci step. -/
theorem fibonacci_recurrence_root_progression (v : ℕ → ℕ)
    (step : ∀ n, v (n+2) = v (n+1)+v n) (cop : ∀ n, (v n).Coprime (v (n+1)))
    {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m) (hp2 : p*p∣m)
    (hs : m∣v s) (hf : m∣Nat.fib j) (sharp : ¬p*m∣Nat.fib j) (b : ℕ) :
    ∃ c<p^b, ∀ t : ℕ, p^b*m∣v (s+j*(c+p^b*t)) := by
  obtain ⟨c,bound,hit⟩ := recurrence_tower v step cop hm hp2 hs hf sharp b
  have ret := (sharp_step_tower hm hp2 hf sharp b).1
  refine ⟨c,bound,fun t => ?_⟩
  rw [show s+j*(c+p^b*t)=s+j*c+(j*p^b)*t by ring,sequence_shift v step]
  exact dvd_add (dvd_mul_of_dvd_right hit _) (dvd_mul_of_dvd_left
    (ret.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))) _)

/-- A Fibonacci return step preserves divisibility of upper-diagonal terms in both directions. -/
theorem lucasFibonacciSum_dvd_shift_iff {m s j : ℕ} (hf : m ∣ Nat.fib j) :
    m ∣ lucasFibonacciSum (s + j) ↔ m ∣ lucasFibonacciSum s := by
  rw [sequence_shift lucasFibonacciSum lucas_fibonacci_sum_recurrence,
    Nat.dvd_add_left (dvd_mul_of_dvd_left hf _)]
  exact ((step_coprime j).of_dvd_left hf).dvd_mul_left

/-- On any positive-step progression, unbounded p-adic valuations are
equivalent to a bounded search at a single explicit Fibonacci valuation. -/
theorem unbounded_prime_powers_iff_finite_test {p : ℕ} [Fact p.Prime]
    (r d : ℕ) (hd : 0 < d) :
    let e := fibonacciStepRank (p ^ 2) d
    let a := (Nat.fib (d * e)).factorization p
    (∀ b : ℕ, ∃ t : ℕ, p ^ b ∣ lucasFibonacciSum (r + d * t)) ↔
      ∃ t < e, p ^ a ∣ lucasFibonacciSum (r + d * t) := by
  dsimp only
  let e := fibonacciStepRank (p ^ 2) d
  let j := d * e
  let a := (Nat.fib j).factorization p
  let m := p ^ a
  have hp : p.Prime := Fact.out
  obtain ⟨he,hf⟩ := rank_spec (p ^ 2) d
  have hj : Nat.fib j ≠ 0 := (Nat.fib_pos.mpr (Nat.mul_pos hd he)).ne'
  have hm : 0 < m := pow_pos hp.pos _
  have hF : m ∣ Nat.fib j := Nat.ordProj_dvd ..
  have hp2 : p * p ∣ m := by
    rw [← pow_two]
    apply pow_dvd_pow
    exact (hp.pow_dvd_iff_le_factorization hj).mp hf
  have hsharp : ¬p * m ∣ Nat.fib j := by
    simpa [m, a, pow_succ'] using Nat.pow_succ_factorization_not_dvd hj hp
  constructor
  · intro h
    obtain ⟨t,ht⟩ := h a
    refine ⟨t % e, Nat.mod_lt _ he, ?_⟩
    have hshift : m ∣ Nat.fib (j * (t / e)) :=
      hF.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))
    apply (lucasFibonacciSum_dvd_shift_iff (s := r + d * (t % e)) hshift).mp
    convert ht using 1
    congr 1
    dsimp [j]
    rw [Nat.mul_assoc, Nat.add_assoc r, ← Nat.mul_add, Nat.mod_add_div]
  · rintro ⟨t,_,ht⟩ b
    obtain ⟨u,_,hu⟩ := tower_of_hit hm hp2 ht hF hsharp b
    refine ⟨t + e * u, (dvd_mul_right (p ^ b) m).trans ?_⟩
    have hidx : r + d * t + j * u = r + d * (t + e * u) := by dsimp only [j]; ring
    rwa [hidx] at hu

/-- The 2-adic valuations on the upper diagonal are bounded by two, while
arbitrarily high powers of three divide terms with index 3 modulo 12. -/
theorem eight_excluded_three_unbounded :
    (∀ n : ℕ, ¬8 ∣ lucasFibonacciSum n) ∧
      ∀ b : ℕ, ∃ t < 3 ^ b, 3 ^ (b + 2) ∣ lucasFibonacciSum (3 + 12 * t) := by
  constructor
  · intro n hn
    have hf : 8 ∣ Nat.fib (6 * (n / 6)) :=
      (by decide : 8 ∣ Nat.fib 6).trans (Nat.fib_dvd _ _ (dvd_mul_right ..))
    have hs := (lucasFibonacciSum_dvd_shift_iff (s := n % 6) hf).mp
    rw [Nat.mod_add_div] at hs
    have hh := hs hn
    have hsmall (a : ℕ) (ha : a < 6) : ¬8 ∣ lucasFibonacciSum a := by
      interval_cases a <;> decide
    exact hsmall _ (Nat.mod_lt _ (by decide)) hh
  · intro b
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    simpa only [pow_add, show 3 ^ 2 = 9 by decide] using
      tower_of_hit (p := 3) (m := 9) (s := 3) (j := 12) (by decide) (by decide)
        (by decide) (by decide) (by decide) b

/-- The return rank along a sharp Fibonacci step increases by the factor
p at every higher level. This depends only on the Fibonacci step. -/
theorem sharp_step_rank {p m j : ℕ} [Fact p.Prime] [NeZero m]
    (hp2 : p*p ∣ m) (hf : m ∣ Nat.fib j) (hsharp : ¬p*m ∣ Nat.fib j) (k : ℕ) :
    fibonacciStepRank (p^k*m) j = p^k := by
  have hp := (Fact.out : p.Prime).pos
  have hm := NeZero.pos m
  induction k with
  | zero =>
    have hle : fibonacciStepRank m j≤1 := rank_le (by decide) (by simpa using hf)
    have hge := (rank_spec m j).1
    simpa using (show fibonacciStepRank m j=1 by omega)
  | succ k ih =>
    let N := p^k*m
    let : NeZero N := ⟨(Nat.mul_pos (pow_pos hp _) hm).ne'⟩
    have hN : p ∣ N := ((dvd_mul_right p p).trans hp2).trans (dvd_mul_left _ _)
    have hh := fibonacciStepRank_prime_mul (p:=p) hN j
    change fibonacciStepRank N j=p^k at ih
    rw [ih,if_neg (sharp_step_tower hm hp2 hf hsharp k).2] at hh
    simpa only [N,pow_succ',Nat.mul_assoc] using hh

/-- At a sharp Fibonacci step, each additional exponent cuts out exactly
one residue class in the progression parameter. -/
theorem sharp_prime_power_lift_class {p m s j : ℕ} [Fact p.Prime] (hm : 0 < m)
    (hp2 : p*p ∣ m) (hs : m ∣ lucasFibonacciSum s) (hf : m ∣ Nat.fib j)
    (hsharp : ¬p*m ∣ Nat.fib j) (b : ℕ) :
    ∃ c < p^b, ∀ t : ℕ, p^b*m ∣ lucasFibonacciSum (s+j*t) ↔ t ≡ c [MOD p^b] := by
  have hp := (Fact.out : p.Prime).pos
  let : NeZero m := ⟨hm.ne'⟩
  have rank := sharp_step_rank hp2 hf hsharp
  let Q := p^b
  let N := Q*m
  let : NeZero N := ⟨(Nat.mul_pos (pow_pos hp _) hm).ne'⟩
  obtain ⟨c,hc,hit⟩ := tower_of_hit hm hp2 hs hf hsharp b
  change c<Q at hc
  change N ∣ lucasFibonacciSum (s+j*c) at hit
  refine ⟨c,hc,?_⟩
  intro t
  have hle : c≤t+Q := by omega
  have hper := lucasFibonacciSum_dvd_shift_iff (s:=s+j*t) (sharp_step_tower hm hp2 hf hsharp b).1
  change N ∣ lucasFibonacciSum (s+j*t+j*Q) ↔ _ at hper
  have he : s+j*t+j*Q = s+j*c+j*(t+Q-c) := by
    have ht : t+Q=c+(t+Q-c) := by omega
    calc
      _ = s+j*(t+Q) := by ring
      _ = s+j*(c+(t+Q-c)) := congrArg (fun v => s+j*v) ht
      _ = _ := by ring
  rw [←hper,he,lucasFibonacciSum_dvd_after_hit_iff hit,rank b,←Nat.modEq_iff_dvd' hle]
  exact ⟨fun h => (h.trans Nat.add_modEq_right).symm,
    fun h => h.symm.trans Nat.add_modEq_right.symm⟩

#print axioms lucasFibonacciSum_dvd_shift_iff
#print axioms fibonacci_recurrence_root_progression
#print axioms sharp_step_rank

#print axioms sharp_prime_power_lift_class


#print axioms eight_excluded_three_unbounded

#print axioms unbounded_prime_powers_iff_finite_test

#print axioms prime_mul_dvd_lucasFibonacciSum_iff
#print axioms prime_mul_lifts_on_class
#print axioms fibonacciStepRank_prime_mul

end Arxiv.«2211.10788»
