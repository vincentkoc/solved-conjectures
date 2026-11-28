import Mathlib
import research.arxiv.«2211.10788».NeighboringLucasFibonacciPrimes

/-!
# Half-index primality certificates for the neighboring Lucas–Fibonacci sums

Doubling an index gives explicit factorizations of both values minus one.
A single modular witness can use the larger factor of each product.
-/

namespace Arxiv.«2211.10788»

/-- An element whose reduction at every prime divisor of `N` has order `H`.
The tests use only the prime divisors of `H`. -/
def HasOrderCertificate (N H : ℕ) : Prop :=
  ∃ b : ZMod N, b^H = 1 ∧
    ∀ q ∈ H.primeFactors, IsUnit (b^(H/q)-1)

/-- Pocklington's order argument with a single witness and the sharp
size condition needed to exclude the least prime divisor. -/
theorem prime_iff_order_certificate (N H : ℕ) (hN : 1 < N) (hH : 0 < H)
    (hd : H ∣ N-1) (hs : N < (H+1)^2) : N.Prime ↔ HasOrderCertificate N H := by
  constructor
  · intro hp
    let : Fact N.Prime := ⟨hp⟩
    obtain ⟨a,ha,haq⟩ := reverse_lucas_primality N hp
    obtain ⟨R,hR⟩ := hd
    refine ⟨a^R,?_,?_⟩
    · rw [←pow_mul,mul_comm R H,←hR,ha]
    · intro q hq
      obtain ⟨hq',hqd,_⟩ := Nat.mem_primeFactors.mp hq
      apply isUnit_iff_ne_zero.mpr
      apply sub_ne_zero.mpr
      rw [←pow_mul,←Nat.mul_div_assoc R hqd,mul_comm R H,←hR]
      exact haq q hq' (hqd.trans ⟨R,hR⟩)
  · rintro ⟨b,hb,hunit⟩
    by_contra hn
    let p := N.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    let : Fact p.Prime := ⟨hp⟩
    let red := ZMod.castHom (Nat.minFac_dvd N) (ZMod p)
    have hpow : (red b)^H = 1 := by rw [←map_pow,hb,map_one]
    have hneq : red b ≠ 0 := by
      intro hz
      rw [hz,zero_pow hH.ne'] at hpow
      exact zero_ne_one hpow
    have ho : orderOf (red b) = H := by
      apply orderOf_eq_of_pow_and_pow_div_prime hH hpow
      intro q hq hdq he
      have hu := (hunit q (Nat.mem_primeFactors.mpr ⟨hq,hdq,hH.ne'⟩)).map red
      rw [map_sub,map_pow,map_one,he,sub_self] at hu
      exact not_isUnit_zero hu
    have hdiv : H ∣ p-1 := ho ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hneq)
    have hle := Nat.le_of_dvd (show 0 < p-1 by have := hp.one_lt; omega) hdiv
    have hh := Nat.pow_le_pow_left (show H+1 ≤ p by omega) 2
    have hmin := Nat.minFac_sq_le_self (by omega : 0 < N) hn
    change p^2 ≤ N at hmin
    omega

#print axioms prime_iff_order_certificate

/-- Factors of the even-index value minus one, read from two consecutive
Fibonacci numbers at the half index. -/
def halfIndexFactors (upper : Bool) (n : ℕ) : ℕ × ℕ :=
  let a := Nat.fib n
  let b := Nat.fib (n+1)
  if upper then
    if n % 2 = 0 then (7*b-a,a) else (3*a+b,2*b-a)
  else
    if n % 2 = 0 then (4*a-b,2*b-a) else (7*b-6*a,a)

theorem halfIndexFactors_product (upper : Bool) (m : ℕ) :
    let n := m+1
    let (H,R) := halfIndexFactors upper n
    (if upper then lucasFibonacciSum (2*n) else lowerNeighborAtAddTwo (2*m)) = H*R+1 := by
  let n := m+1
  let a := Nat.fib n
  let b := Nat.fib (n+1)
  have hmon : a ≤ b := Nat.fib_mono (by omega)
  have hb : b ≤ 2*a := by
    change Nat.fib (m+2) ≤ 2*Nat.fib (m+1)
    rw [Nat.fib_add_two]
    have := Nat.fib_mono (show m ≤ m+1 by omega)
    omega
  have hf : Nat.fib (2*n) = a*(2*b-a) := Nat.fib_two_mul n
  have hf' : Nat.fib (2*n+1) = b^2+a^2 := Nat.fib_two_mul_add_one n
  have hU : lucasFibonacciSum (2*n) = 3*Nat.fib (2*n)+Nat.fib (2*n+1) := by
    simp only [lucasFibonacciSum,Nat.fib_add_two]; omega
  have hV : lowerNeighborAtAddTwo (2*m) + Nat.fib (2*n+1) = 4*Nat.fib (2*n) := by
    have e : 2*n = 2*m+2 := by dsimp [n]; omega
    rw [e,lowerNeighborAtAddTwo]
    have e₁ := Nat.fib_add_two (n := 2*m)
    have e₂ := Nat.fib_add_two (n := 2*m+1)
    norm_num [Nat.add_assoc] at e₂ ⊢
    omega
  have hc := fib_pair_norm n
  change (b:ℤ)^2-a*b-(a:ℤ)^2 = (-1)^n at hc
  rw [hf,hf'] at hU hV
  change (if upper then lucasFibonacciSum (2*n) else lowerNeighborAtAddTwo (2*m)) =
    (halfIndexFactors upper n).1*(halfIndexFactors upper n).2+1
  have ha2 : a ≤ 2*b := by omega
  have ha7 : a ≤ 7*b := by omega
  have hb4 : b ≤ 4*a := by omega
  have hb7 : 6*a ≤ 7*b := by omega
  by_cases hpar : n%2=0
  · rw [((Nat.even_iff).2 hpar).neg_one_pow] at hc
    cases upper <;> simp only [halfIndexFactors, Bool.false_eq_true,if_false,if_true,hpar]
    all_goals
      change _ = _* _ + 1
      first | change lowerNeighborAtAddTwo (2*m) = (4*a-b)*(2*b-a)+1
            | change lucasFibonacciSum (2*n) = (7*b-a)*a+1
      zify [hb4,ha2,ha7] at hU hV ⊢
      nlinarith only [hU,hV,hc]
  · have odd : Odd n := Nat.odd_iff.mpr (by omega)
    rw [odd.neg_one_pow] at hc
    cases upper <;> simp only [halfIndexFactors, Bool.false_eq_true,if_false,if_true,hpar]
    all_goals
      first | change lowerNeighborAtAddTwo (2*m) = (7*b-6*a)*a+1
            | change lucasFibonacciSum (2*n) = (3*a+b)*(2*b-a)+1
      zify [ha2,hb7] at hU hV ⊢
      nlinarith only [hU,hV,hc]

#print axioms halfIndexFactors_product

/-- The larger of the two half-index factors suffices to certify either
neighbor at any positive even index. No factors of the complementary part
of the value minus one are needed. -/
theorem even_neighbor_prime_iff_halfIndex_certificate (upper : Bool) (m : ℕ) :
    let n := m+1
    let N := if upper then lucasFibonacciSum (2*n) else lowerNeighborAtAddTwo (2*m)
    let f := halfIndexFactors upper n
    N.Prime ↔ HasOrderCertificate N (max f.1 f.2) := by
  let n := m+1
  let N := if upper then lucasFibonacciSum (2*n) else lowerNeighborAtAddTwo (2*m)
  let f := halfIndexFactors upper n
  change N.Prime ↔ HasOrderCertificate N (max f.1 f.2)
  have he : N = f.1*f.2+1 := halfIndexFactors_product upper m
  have hN : 1 < N := by
    have hf : 0 < Nat.fib (2*n) := Nat.fib_pos.mpr (by dsimp [n]; omega)
    have hf' : 0 < Nat.fib (2*m+2) := Nat.fib_pos.mpr (by omega)
    cases upper <;> simp only [N,lucasFibonacciSum,lowerNeighborAtAddTwo,
      Bool.false_eq_true,if_false,if_true] <;> omega
  have hp : 0 < f.1*f.2 := by omega
  have hh := Nat.pos_of_mul_pos_right hp
  have hr := Nat.pos_of_mul_pos_left hp
  have hx := Nat.mul_le_mul (le_max_left f.1 f.2) (le_max_right f.1 f.2)
  apply prime_iff_order_certificate N _ hN (lt_of_lt_of_le hh (le_max_left ..))
  · rw [he,Nat.add_sub_cancel]
    rcases le_total f.1 f.2 with h|h
    · rw [max_eq_right h]; exact dvd_mul_left _ _
    · rw [max_eq_left h]; exact dvd_mul_right _ _
  · have hz : 0 < max f.1 f.2 := lt_of_lt_of_le hh (le_max_left ..)
    nlinarith

#print axioms even_neighbor_prime_iff_halfIndex_certificate

/-- The half-index certificate for the chosen neighbor at index `2(m+1)`. -/
def halfIndexCertificateAt (upper : Bool) (m : ℕ) : Prop :=
  let n := m+1
  let N := if upper then lucasFibonacciSum (2*n) else lowerNeighborAtAddTwo (2*m)
  let f := halfIndexFactors upper n
  HasOrderCertificate N (max f.1 f.2)

/-- Both neighbors at index `m+2` are prime precisely when the index is
even and each passes its half-index certificate. -/
theorem neighboring_primes_iff_halfIndex_certificates (m : ℕ) :
    ((lucasFibonacciSum (m+2)).Prime ∧ (lowerNeighborAtAddTwo m).Prime) ↔
      ∃ k, m = 2*k ∧ halfIndexCertificateAt true k ∧ halfIndexCertificateAt false k := by
  have pair (k : ℕ) : ((lucasFibonacciSum (2*k+2)).Prime ∧ (lowerNeighborAtAddTwo (2*k)).Prime) ↔
      (halfIndexCertificateAt true k ∧ halfIndexCertificateAt false k) := by
    have hp := even_neighbor_prime_iff_halfIndex_certificate true k
    have hq := even_neighbor_prime_iff_halfIndex_certificate false k
    change (lucasFibonacciSum (2*(k+1))).Prime ↔ halfIndexCertificateAt true k at hp
    change (lowerNeighborAtAddTwo (2*k)).Prime ↔ halfIndexCertificateAt false k at hq
    simpa only [Nat.mul_add,Nat.mul_one] using and_congr hp hq
  constructor
  · intro hp
    have h := (neighboring_primes_iff_semiprime m).mp hp
    have he : m = 2*(m/2) := by
      rcases h with h|⟨h,_⟩
      · omega
      · simp only [Finset.mem_insert,Finset.mem_singleton] at h
        omega
    exact ⟨m/2,he,(pair _).mp (by simpa only [←he] using hp)⟩
  · rintro ⟨k,rfl,hU,hV⟩
    exact (pair k).mpr ⟨hU,hV⟩

#print axioms neighboring_primes_iff_halfIndex_certificates

end Arxiv.«2211.10788»
