import Mathlib
import research.arxiv.«2211.10788».NeighboringLucasFibonacciPrimes

/-! Prime values on the two Hosoya diagonals and the form x² + 11y². -/

namespace Arxiv.«2211.10788»

/-- Representation by the integral binary form x² + dy². -/
def NormFormRepresents (d n : ℤ) : Prop := ∃ x y : ℤ, x^2 + d*y^2 = n

private lemma normForm_mul {d m n : ℤ} (hm : NormFormRepresents d m)
    (hn : NormFormRepresents d n) : NormFormRepresents d (m*n) := by
  obtain ⟨x,y,rfl⟩ := hm
  obtain ⟨a,b,rfl⟩ := hn
  exact ⟨a*x + d*b*y, a*y - b*x, by ring⟩

/-- A represented rational prime can be cancelled from any represented product.
Choosing the conjugate if needed makes both coordinates divisible by p. -/
theorem normForm_prime_mul_iff {p : ℕ} (hp : p.Prime) {d m : ℤ}
    (hrep : NormFormRepresents d p) :
    NormFormRepresents d ((p : ℤ)*m) ↔ NormFormRepresents d m := by
  refine ⟨?_, normForm_mul hrep⟩
  rintro ⟨a,b,hab⟩
  obtain ⟨x,y,hxy⟩ := hrep
  let : Fact p.Prime := ⟨hp⟩
  have hxy' : (x : ZMod p)^2 + (d : ZMod p)*y^2 = 0 := by
    simpa using congrArg (Int.castRingHom (ZMod p)) hxy
  have hab' : (a : ZMod p)^2 + (d : ZMod p)*b^2 = 0 := by
    simpa using congrArg (Int.castRingHom (ZMod p)) hab
  have hy : (y : ZMod p) ≠ 0 := by
    intro hy
    have hx : (x : ZMod p) = 0 := by simpa [hy] using hxy'
    obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx
    obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy
    have hdiv : (p : ℤ)^2 ∣ p := ⟨u^2 + d*v^2, by
      calc
        (p : ℤ) = x^2+d*y^2 := hxy.symm
        _ = _ := by rw [hu,hv]; ring⟩
    have hnat : p^2 ∣ p := by exact_mod_cast hdiv
    have hle := Nat.le_of_dvd hp.pos hnat
    nlinarith [hp.two_le]
  have prod : ((a : ZMod p)*y-b*x) * ((a : ZMod p)*y+b*x) = 0 := by
    linear_combination (y : ZMod p)^2 * hab' - (b : ZMod p)^2 * hxy'
  obtain ⟨e,he,he0,hcross⟩ : ∃ e : ℤ, e^2 = y^2 ∧ (e : ZMod p) ≠ 0 ∧
      (a : ZMod p)*e - b*x = 0 := by
    rcases mul_eq_zero.mp prod with h|h
    · exact ⟨y,rfl,hy,h⟩
    · refine ⟨-y,by ring, by simpa using hy, ?_⟩
      push_cast
      linear_combination -h
  have hen : x^2 + d*e^2 = p := he ▸ hxy
  have hen' : (x : ZMod p)^2 + (d : ZMod p)*e^2 = 0 := by
    simpa using congrArg (Int.castRingHom (ZMod p)) hen
  have dot : (a : ZMod p)*x+d*b*e = 0 := by
    apply (mul_eq_zero.mp (show (e : ZMod p)*((a : ZMod p)*x+d*b*e) = 0 by
      linear_combination (x : ZMod p)*hcross + (b : ZMod p)*hen')).resolve_left he0
  obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a*x + d*b*e) p).mp (by simpa using dot)
  obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a*e - b*x) p).mp (by simpa using hcross)
  refine ⟨u,v,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero))
  calc
    (p : ℤ)^2 * (u^2+d*v^2) = (p*u)^2 + d*(p*v)^2 := by ring
    _ = (a*x + d*b*e)^2 + d*(a*e - b*x)^2 := by rw [hu,hv]
    _ = (a^2+d*b^2)*(x^2+d*e^2) := by ring
    _ = _ := by rw [hab,hen]; ring

private lemma normForm_mul_iff_of_factors (n : ℕ) (hn : 0 < n) {d m : ℤ}
    (hrep : ∀ p : ℕ, p.Prime → p ∣ n → NormFormRepresents d p) :
    NormFormRepresents d ((n : ℤ)*m) ↔ NormFormRepresents d m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · simp [h1]
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : p ∣ n := Nat.minFac_dvd n
    let k := n / p
    have he : p*k = n := Nat.mul_div_cancel' hpd
    have hk : k < n := Nat.div_lt_self hn hp.one_lt
    have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hn hpd) hp.pos
    have hkd : k ∣ n := he ▸ dvd_mul_left _ _
    have ih' := ih k hk hkpos (fun q hq hqk => hrep q hq (hqk.trans hkd))
    have h : (n : ℤ)*m = (p : ℤ)*(k*m) := by
      conv_lhs => rw [← he, Nat.cast_mul]
      ring
    exact h ▸ (normForm_prime_mul_iff hp (hrep p hp hpd)).trans ih'

private lemma three_not_represented : ¬ NormFormRepresents 11 3 := by
  rintro ⟨x,y,h⟩
  have hx : x^2 = 3 := by have := sq_nonneg x; have := sq_nonneg y; omega
  have hz : (x : ZMod 4)^2 = 3 := by simpa using congrArg (Int.castRingHom (ZMod 4)) hx
  exact (by decide : ∀ z : ZMod 4, z^2 ≠ 3) _ hz

private lemma odd_norms (n : ℕ) :
    NormFormRepresents 11 ((lucasFibonacciSum (2*n+1) : ℤ)*3) ∧
    NormFormRepresents 11 ((lowerNeighborAtAddTwo (2*n+1) : ℤ)*3) := by
  let a : ℤ := Nat.fib n
  let b : ℤ := Nat.fib (n+1)
  have h₁ : (Nat.fib (2*n+1) : ℤ) = b^2+a^2 := by
    dsimp only [a,b]
    exact_mod_cast Nat.fib_two_mul_add_one n
  have h₂ : (Nat.fib (2*n+1+2) : ℤ) = (a+b)^2+b^2 := by
    rw [show 2*n+1+2 = 2*(n+1)+1 by omega, Nat.fib_two_mul_add_one, Nat.fib_add_two]
    push_cast
    rfl
  constructor
  · refine ⟨3*a+b,b,?_⟩
    simp only [lucasFibonacciSum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h₁, h₂]
    ring
  · refine ⟨3*a+2*b,b,?_⟩
    simp only [lowerNeighborAtAddTwo, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h₁, h₂]
    ring

private lemma even_upper_mod_four (n : ℕ) : lucasFibonacciSum (2*n) % 4 ≠ 3 := by
  let a : ℤ := Nat.fib n
  let b : ℤ := Nat.fib (n+1)
  have h₁ : (Nat.fib (2*n) : ℤ) = a*(2*b-a) := by
    have h : Nat.fib n ≤ 2*Nat.fib (n+1) := by
      have : Nat.fib n ≤ Nat.fib (n+1) := Nat.fib_mono n.le_succ
      omega
    rw [Nat.fib_two_mul]
    push_cast [h]
    rfl
  have h₂ : (Nat.fib (2*n+1) : ℤ) = b^2+a^2 := by
    dsimp only [a,b]
    exact_mod_cast Nat.fib_two_mul_add_one n
  have he : (lucasFibonacciSum (2*n) : ℤ) = (b+3*a)^2-11*a^2 := by
    simp only [lucasFibonacciSum, Nat.fib_add_two, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, h₁, h₂]
    ring
  have z := congrArg (Int.castRingHom (ZMod 4)) he
  have bad : ∀ x y : ZMod 4, x^2-11*y^2 ≠ 3 := by decide
  intro h
  have hz : (lucasFibonacciSum (2*n) : ZMod 4) = 3 :=
    (ZMod.natCast_eq_natCast_iff ..).mpr (show lucasFibonacciSum (2*n) ≡ 3 [MOD 4] from h)
  apply bad ((b+3*a : ℤ) : ZMod 4) (a : ZMod 4)
  simpa using z.symm.trans (by simpa using hz)

private lemma lower_mod_eleven (n : ℕ) : (lowerNeighborAtAddTwo n : ZMod 11) = 2*8^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    have step : lowerNeighborAtAddTwo (n+2) = lowerNeighborAtAddTwo n + lowerNeighborAtAddTwo (n+1) := by
      simp only [lowerNeighborAtAddTwo, Nat.fib_add_two]
      omega
    rw [step, Nat.cast_add, h₀, h₁, pow_succ (8 : ZMod 11) (n+1), pow_succ]
    have h8 : (8 : ZMod 11)^2 = 8+1 := by decide
    linear_combination (-(2 * (8 : ZMod 11)^n)) * h8

private lemma even_lower_not_norm (n : ℕ) : ¬NormFormRepresents 11 (lowerNeighborAtAddTwo (2*n)) := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  rintro ⟨x,y,h⟩
  have hr : (x : ZMod 11)^2 = (lowerNeighborAtAddTwo (2*n) : ZMod 11) := by
    simpa [show (11 : ZMod 11) = 0 by decide] using congrArg (Int.castRingHom (ZMod 11)) h
  rw [lower_mod_eleven, mul_comm 2 n, pow_mul] at hr
  have bad : ∀ z w : ZMod 11, z ≠ 0 → w^2 ≠ 2*z^2 := by decide
  exact bad _ _ (pow_ne_zero _ (by decide : (8 : ZMod 11) ≠ 0)) hr

private lemma upper_pos (n : ℕ) : 0 < lucasFibonacciSum n := by
  have := Nat.fib_pos.mpr (show 0 < n+2 by omega)
  unfold lucasFibonacciSum
  omega

private lemma lower_pos (n : ℕ) : 0 < lowerNeighborAtAddTwo n := by
  have := Nat.fib_pos.mpr (show 0 < n+2 by omega)
  unfold lowerNeighborAtAddTwo
  omega

private lemma factor_of_three_norm {N : ℕ} (hN : 0 < N) (h : NormFormRepresents 11 ((N : ℤ)*3)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ ¬NormFormRepresents 11 p := by
  by_contra! hrep
  exact three_not_represented ((normForm_mul_iff_of_factors N hN hrep).mp h)

/-- Every odd-index upper value and every lower value from physical index two onward
has a prime divisor outside the form x²+11y². -/
theorem hosoya_prime_factor_outside_principal_form (n : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ lucasFibonacciSum (2*n+1) ∧ ¬NormFormRepresents 11 p) ∧
    (∃ p : ℕ, p.Prime ∧ p ∣ lowerNeighborAtAddTwo n ∧ ¬NormFormRepresents 11 p) := by
  refine ⟨factor_of_three_norm (upper_pos _) (odd_norms n).1, ?_⟩
  rcases Nat.even_or_odd n with he|ho
  · obtain ⟨k,hk⟩ := he
    rw [← two_mul k] at hk
    subst n
    by_contra! hrep
    apply even_lower_not_norm k
    have hn : NormFormRepresents 11 (1 : ℤ) := ⟨1,0,by norm_num⟩
    simpa using (normForm_mul_iff_of_factors (lowerNeighborAtAddTwo (2*k)) (lower_pos _) hrep).mpr hn
  · obtain ⟨k,rfl⟩ := ho
    exact factor_of_three_norm (lower_pos _) (odd_norms k).2

/-- A prime x²+11y² on the upper diagonal must occur at an even index and be 1 modulo 4. -/
theorem upper_represented_prime_restriction {p n : ℕ} (hp : p.Prime)
    (hrep : NormFormRepresents 11 p) (hv : lucasFibonacciSum n = p) :
    Even n ∧ p % 4 = 1 := by
  have hEven : Even n := by
    by_contra ho
    obtain ⟨k,rfl⟩ := Nat.not_even_iff_odd.mp ho
    obtain ⟨q,hq,hqd,hbad⟩ := (hosoya_prime_factor_outside_principal_form k).1
    rw [hv] at hqd
    exact hbad ((hp.eq_one_or_self_of_dvd q hqd).resolve_left hq.ne_one ▸ hrep)
  refine ⟨hEven,?_⟩
  obtain ⟨k,hk⟩ := hEven
  rw [← two_mul k] at hk
  have h3 := even_upper_mod_four k
  rw [← hk,hv] at h3
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨x,y,h⟩ := hrep
    have h₂ : (x : ZMod 11)^2 = 2 := by
      simpa [show (11 : ZMod 11) = 0 by decide] using congrArg (Int.castRingHom (ZMod 11)) h
    exact (by decide : ∀ z : ZMod 11, z^2 ≠ 2) _ h₂
  have := hp.odd_of_ne_two hp2
  rw [Nat.odd_iff] at this
  omega

/-- A prime represented by x²+11y² occurs nowhere on the lower diagonal, including
the initial value F₁+L₀ = 3. -/
theorem lower_represented_prime_excluded {p : ℕ} (hp : p.Prime) (hrep : NormFormRepresents 11 p) :
    p ≠ 3 ∧ ∀ n, lowerNeighborAtAddTwo n ≠ p := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact three_not_represented hrep
  intro n h
  obtain ⟨q,hq,hqd,hbad⟩ := (hosoya_prime_factor_outside_principal_form n).2
  rw [h] at hqd
  exact hbad ((hp.eq_one_or_self_of_dvd q hqd).resolve_left hq.ne_one ▸ hrep)

/-- The same primitive form excludes a prime from both diagonals. -/
theorem four_eleven_form_excluded {p : ℕ} (hp : p.Prime) (x y : ℤ)
    (h : 4*x^2 + 11*y^2 = p) :
    (∀ n, lucasFibonacciSum n ≠ p) ∧ p ≠ 3 ∧ ∀ n, lowerNeighborAtAddTwo n ≠ p := by
  have hr : NormFormRepresents 11 p := ⟨2*x,y,by linear_combination h⟩
  refine ⟨?_, lower_represented_prime_excluded hp hr⟩
  intro n hn
  have h1 := (upper_represented_prime_restriction hp hr hn).2
  have hz : (p : ZMod 4) = 1 :=
    (ZMod.natCast_eq_natCast_iff ..).mpr (show p ≡ 1 [MOD 4] from h1)
  have he : 4*(x : ZMod 4)^2 + 11*(y : ZMod 4)^2 = 1 := by
    simpa using (congrArg (Int.castRingHom (ZMod 4)) h).trans (by simpa using hz)
  exact (by decide : ∀ a b : ZMod 4, 4*a^2 + 11*b^2 ≠ 1) _ _ he

example : 103 ∣ lucasFibonacciSum 75 ∧ ∀ n, lucasFibonacciSum n ≠ 103 := by
  exact ⟨by norm_num [lucasFibonacciSum],
    (four_eleven_form_excluded (p := 103) (by decide) 1 3 (by decide)).1⟩

example : 53 ∣ lowerNeighborAtAddTwo 9 ∧ ∀ n, lowerNeighborAtAddTwo n ≠ 53 := by
  exact ⟨by decide, (lower_represented_prime_excluded (p := 53) (by decide)
    ⟨3, 2, by decide⟩).2⟩

#print axioms normForm_prime_mul_iff
#print axioms hosoya_prime_factor_outside_principal_form
#print axioms upper_represented_prime_restriction
#print axioms lower_represented_prime_excluded
#print axioms four_eleven_form_excluded

end Arxiv.«2211.10788»
