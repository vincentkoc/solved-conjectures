import Mathlib
import research.arxiv.«2211.10788».NeighboringLucasFibonacciPrimes

/-! A cube obstruction for the odd-index Hosoya diagonals. -/

namespace Arxiv.«2211.10788»

open QuadraticAlgebra

/-- The integer ring of the quadratic field of discriminant −11. -/
abbrev ElevenRing := QuadraticAlgebra ℤ (-3) 1

namespace ElevenRing

theorem four_norm (z : ElevenRing) :
    4 * z.norm = (2 * z.re + z.im) ^ 2 + 11 * z.im ^ 2 := by
  rw [norm_def]
  ring

theorem norm_nonneg' (z : ElevenRing) : 0 ≤ z.norm := by
  nlinarith [four_norm z, sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]

theorem norm_pos' {z : ElevenRing} (h : z ≠ 0) : 0 < z.norm := by
  by_contra! hn
  have hi : z.im = 0 := by
    by_contra hy
    nlinarith [four_norm z, sq_nonneg (2 * z.re + z.im), sq_pos_of_ne_zero hy]
  apply h
  apply QuadraticAlgebra.ext _ hi
  change z.re = 0
  have hf := four_norm z
  rw [hi] at hf
  by_contra hr
  nlinarith [sq_pos_of_ne_zero hr]

private noncomputable def nearest (x m : ℤ) : ℤ := round ((x : ℚ) / m)

private theorem nearest_bounds (x : ℤ) {m : ℤ} (hm : 0 < m) :
    -m ≤ 2 * (x - m * nearest x m) ∧ 2 * (x - m * nearest x m) ≤ m := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have h := abs_le.mp (abs_sub_round ((x : ℚ) / m))
  change -(1 / 2 : ℚ) ≤ (x : ℚ) / m - nearest x m ∧
    (x : ℚ) / m - nearest x m ≤ 1 / 2 at h
  obtain ⟨hl, hr⟩ := h
  field_simp [hm'] at hl hr
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩

private noncomputable def elevenQuot (a b : ElevenRing) : ElevenRing :=
  let v := a * star b
  let m := b.norm
  let y := nearest v.im m
  ⟨nearest (2 * v.re + v.im - m * y) (2 * m), y⟩

private theorem quotient_error (a b : ElevenRing) (hb : b ≠ 0) :
    (a - b * elevenQuot a b).norm < b.norm := by
  let v := a * star b
  let m := b.norm
  let q := elevenQuot a b
  let w := v - algebraMap ℤ ElevenRing m * q
  have hm : 0 < m := norm_pos' hb
  have hy := nearest_bounds v.im hm
  have hx := nearest_bounds (2 * v.re + v.im - m * q.im) (show 0 < 2 * m by omega)
  change -m ≤ 2 * (v.im - m * q.im) ∧ 2 * (v.im - m * q.im) ≤ m at hy
  change -(2 * m) ≤ 2 * (2 * v.re + v.im - m * q.im - 2 * m * q.re) ∧
    2 * (2 * v.re + v.im - m * q.im - 2 * m * q.re) ≤ 2 * m at hx
  have hwr : w.re = v.re - m * q.re := by simp [w]
  have hwi : w.im = v.im - m * q.im := by simp [w]
  have hy' : -m ≤ 2 * w.im ∧ 2 * w.im ≤ m := by rw [hwi]; exact hy
  have hx' : -m ≤ 2 * w.re + w.im ∧ 2 * w.re + w.im ≤ m := by
    rw [hwr, hwi]
    constructor <;> linarith
  have bound {s : ℤ} (hs : -m ≤ s ∧ s ≤ m) : s ^ 2 ≤ m ^ 2 := by
    nlinarith [mul_nonneg (by linarith [hs.1] : 0 ≤ m + s) (sub_nonneg.mpr hs.2)]
  have hw : w = (a - b * q) * star b := by
    change a * star b - algebraMap ℤ ElevenRing b.norm * q = _
    rw [algebraMap_norm_eq_mul_star]
    ring
  have hn : w.norm = (a - b * q).norm * m := by rw [hw, map_mul, QuadraticAlgebra.norm_star]
  have sq := four_norm w
  rw [hn] at sq
  change (a - b * q).norm < m
  by_contra! hf
  nlinarith [bound hx', bound hy', mul_le_mul_of_nonneg_right hf hm.le,
    mul_pos hm hm]

noncomputable scoped instance : EuclideanDomain ElevenRing :=
  { (inferInstance : CommRing ElevenRing), (inferInstance : Nontrivial ElevenRing) with
    quotient := elevenQuot
    remainder := fun a b => a - b * elevenQuot a b
    quotient_zero := by intro a; ext <;> simp [elevenQuot, nearest]
    quotient_mul_add_remainder_eq := fun _ _ => by ring
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (fun z : ElevenRing => z.norm.natAbs)).wf
    remainder_lt := by
      intro a b hb
      exact_mod_cast (show ((a - b * elevenQuot a b).norm.natAbs : ℤ) < (b.norm.natAbs : ℤ) by
        simpa only [Int.natCast_natAbs, abs_of_nonneg (norm_nonneg' _)] using quotient_error a b hb)
    mul_left_not_lt := by
      intro a b hb
      change ¬ (a * b).norm.natAbs < a.norm.natAbs
      rw [map_mul, Int.natAbs_mul]
      have hpos : 0 < b.norm.natAbs := Int.natAbs_pos.mpr (norm_pos' hb).ne'
      exact Nat.not_lt.mpr (Nat.le_mul_of_pos_right _ hpos) }

theorem unit_im_zero (u : ElevenRingˣ) : (u : ElevenRing).im = 0 := by
  have hu := Int.isUnit_iff.mp (u.isUnit.map (QuadraticAlgebra.norm : ElevenRing →* ℤ))
  have hn := norm_nonneg' (u : ElevenRing)
  have hf := four_norm (u : ElevenRing)
  by_contra hi
  have hi' : 0 < (u : ElevenRing).im ^ 2 := sq_pos_of_ne_zero hi
  rcases hu with h | h <;> nlinarith [sq_nonneg (2 * (u : ElevenRing).re + (u : ElevenRing).im)]

end ElevenRing

open ElevenRing

/-- A common divisor of the trace and a cube root of the norm would divide both coordinates.
For the ramified prime 11 the argument uses two powers of 11 in the trace square. -/
private theorem trace_coprime_root (z : ElevenRing) {t : ℤ}
    (hc : IsCoprime z.re z.im) (he : z.norm = t ^ 3) : IsCoprime (2 * z.re + z.im) t := by
  have h := four_norm z
  rw [he] at h
  apply isCoprime_of_prime_dvd
  · rintro ⟨_, ht⟩
    have hz : z = 0 := by
      by_contra hz
      have := norm_pos' hz
      simp [ht] at he
      omega
    obtain ⟨u, v, huv⟩ := hc
    simp [hz] at huv
  intro p hp htrace ht
  have h11y : p ∣ 11 * z.im ^ 2 := by
    obtain ⟨s, hs⟩ := ht
    obtain ⟨r, hr⟩ := htrace
    rw [hs, hr] at h
    exact ⟨4 * p ^ 2 * s ^ 3 - p * r ^ 2, by linear_combination -h⟩
  have hy : p ∣ z.im := by
    rcases hp.dvd_or_dvd h11y with h11 | hy
    · have p11 : Prime (11 : ℤ) := by decide
      have hass := hp.associated_of_dvd p11 h11
      obtain ⟨s, hs⟩ := hass.dvd'.trans ht
      obtain ⟨r, hr⟩ := hass.dvd'.trans htrace
      rw [hr, hs] at h
      apply h11.trans
      apply p11.dvd_of_dvd_pow (n := 2)
      exact ⟨44 * s ^ 3 - r ^ 2, by nlinarith only [h]⟩
    · exact hp.dvd_of_dvd_pow hy
  apply hp.not_isUnit (hc.isUnit_of_dvd' _ hy)
  apply hp.dvd_of_dvd_pow (n := 2)
  obtain ⟨s, hs⟩ := ht
  obtain ⟨k, hk⟩ := hy
  refine ⟨p ^ 2 * s ^ 3 - k * (z.re + 3 * z.im), ?_⟩
  rw [norm_def, hk, hs] at he
  rw [hk]
  linear_combination he

private theorem cube_im_even (z : ElevenRing) : (2 : ℤ) ∣ (z ^ 3).im := by
  have h : (z ^ 3).im = 3 * z.re ^ 2 * z.im + 3 * z.re * z.im ^ 2 - 2 * z.im ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, im_mul, re_mul]
    ring
  rw [h]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  push_cast
  exact (by decide : ∀ x y : ZMod 2, 3 * x ^ 2 * y + 3 * x * y ^ 2 - 2 * y ^ 3 = 0) _ _

private theorem even_im_of_norm_cube (z : ElevenRing) {t : ℤ}
    (hc : IsCoprime z.re z.im) (he : z.norm = t ^ 3) : (2 : ℤ) ∣ z.im := by
  classical
  let := EuclideanDomain.gcdMonoid ElevenRing
  have hcop : IsCoprime (2 * z.re + z.im) (t ^ 3) := (trace_coprime_root z hc he).pow_right
  have hsum : algebraMap ℤ ElevenRing (2 * z.re + z.im) = z + star z := by
    ext <;> simp
    ring
  have hprod : algebraMap ℤ ElevenRing (t ^ 3) = z * star z := by
    rw [← he, algebraMap_norm_eq_mul_star]
  have hbez := hcop.map (algebraMap ℤ ElevenRing)
  rw [hsum, hprod] at hbez
  have hd := gcd_dvd_left z (star z)
  have hu := hbez.isUnit_of_dvd' (dvd_add hd (gcd_dvd_right z (star z)))
    (dvd_mul_of_dvd_left hd _)
  obtain ⟨w, u, hu'⟩ := exists_associated_pow_of_mul_eq_pow hu (hprod.symm.trans (map_pow _ _ _))
  rw [← hu', im_mul, unit_im_zero]
  simpa using dvd_mul_of_dvd_left (cube_im_even w) (u : ElevenRing).re

/-- The primitive positive binary form of discriminant −44 occurring on both odd
Hosoya diagonals never represents an integer cube. -/
theorem hosoya_primitive_form_ne_cube {a b : ℤ} (hab : IsCoprime a b) (t : ℤ) :
    3 * a ^ 2 + 2 * a * b + 4 * b ^ 2 ≠ t ^ 3 := by
  intro he
  have p2 : Prime (2 : ℤ) := by decide
  by_cases ha : (2 : ℤ) ∣ a
  · have hb : ¬ (2 : ℤ) ∣ b := fun h => p2.not_isUnit (hab.isUnit_of_dvd' ha h)
    obtain ⟨s, hs⟩ := ha
    obtain ⟨v, hv⟩ : ∃ v : ℤ, b = 2 * v + 1 := ⟨b / 2, by omega⟩
    rw [hs, hv] at he
    have hz := congrArg (Int.castRingHom (ZMod 8)) he
    simp only [map_add, map_mul, map_pow, map_one, map_ofNat, Int.coe_castRingHom] at hz
    exact (by decide : ∀ s v t : ZMod 8,
      3 * (2*s)^2 + 2*(2*s)*(2*v+1) + 4*(2*v+1)^2 ≠ t^3) _ _ _ hz
  · let z : ElevenRing := ⟨2 * b, a⟩
    have hc : IsCoprime z.re z.im :=
      (p2.irreducible.coprime_iff_not_dvd.mpr ha).mul_left hab.symm
    have hn : z.norm = t ^ 3 := by
      change 2*b*(2*b) + 1*(2*b)*a - (-3)*a*a = _
      linear_combination he
    exact ha (even_im_of_norm_cube z hc hn)

/-- On both odd-index diagonals the half-index Fibonacci pair gives a primitive
representation by the quadratic form of discriminant −44. -/
theorem odd_hosoya_form_witnesses (n : ℕ) :
    (∃ a b : ℤ, IsCoprime a b ∧ 3*a^2+2*a*b+4*b^2 = lucasFibonacciSum (2*n+1)) ∧
    (∃ a b : ℤ, IsCoprime a b ∧ 3*a^2+2*a*b+4*b^2 = lowerNeighborAtAddTwo (2*n+1)) := by
  let a : ℤ := Nat.fib n
  let b : ℤ := Nat.fib (n+1)
  have hc : IsCoprime a b := (Nat.fib_coprime_fib_succ n).isCoprime
  have h₁ : (Nat.fib (2*n+1) : ℤ) = b^2+a^2 := by
    dsimp only [a, b]
    exact_mod_cast Nat.fib_two_mul_add_one n
  have h₂ : (Nat.fib (2*n+1+2) : ℤ) = (a+b)^2+b^2 := by
    rw [show 2*n+1+2 = 2*(n+1)+1 by omega, Nat.fib_two_mul_add_one, Nat.fib_add_two]
    push_cast
    rfl
  have hl : IsCoprime (a+b) (-b) := by
    obtain ⟨u, v, huv⟩ := hc
    exact ⟨u, u-v, by linear_combination huv⟩
  refine ⟨⟨a,b,hc,?_⟩,⟨a+b,-b,hl,?_⟩⟩ <;>
    simp only [lucasFibonacciSum, lowerNeighborAtAddTwo, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, h₁, h₂] <;> ring

/-- Both odd-index diagonals exclude cubes. The lower term displayed here is at
actual index `2*n+3` because its defining index is shifted by two. -/
theorem odd_hosoya_diagonals_ne_cube (n : ℕ) (t : ℤ) :
    (lucasFibonacciSum (2*n+1) : ℤ) ≠ t^3 ∧
    (lowerNeighborAtAddTwo (2*n+1) : ℤ) ≠ t^3 := by
  obtain ⟨⟨a,b,hc,hu⟩,⟨c,d,hd,hv⟩⟩ := odd_hosoya_form_witnesses n
  rw [←hu,←hv]
  exact ⟨hosoya_primitive_form_ne_cube hc t, hosoya_primitive_form_ne_cube hd t⟩

/-- At actual index `2*n+1`, the lower sum is `3F_{2n+1}−F_{2n}` since
`L_k = 2F_{k+1}−F_k`. This includes its initial value 3. -/
theorem odd_lower_lucas_fibonacci_sum_ne_cube (n : ℕ) (t : ℤ) :
    3 * (Nat.fib (2*n+1) : ℤ) - Nat.fib (2*n) ≠ t^3 := by
  cases n with
  | zero =>
    simpa using hosoya_primitive_form_ne_cube (a := 1) (b := 0) ⟨1, 0, by norm_num⟩ t
  | succ n =>
    have he : 3 * (Nat.fib (2*(n+1)+1) : ℤ) - Nat.fib (2*(n+1)) =
        lowerNeighborAtAddTwo (2*n+1) := by
      rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,
        show 2*(n+1) = (2*n+1)+1 by omega]
      simp only [lowerNeighborAtAddTwo, Nat.fib_add_two, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [he]
    exact (odd_hosoya_diagonals_ne_cube n t).2

#print axioms ElevenRing.four_norm
#print axioms ElevenRing.norm_nonneg'
#print axioms ElevenRing.norm_pos'
#print axioms ElevenRing.unit_im_zero
#print axioms odd_hosoya_form_witnesses
#print axioms odd_lower_lucas_fibonacci_sum_ne_cube
#print axioms hosoya_primitive_form_ne_cube
#print axioms odd_hosoya_diagonals_ne_cube

end Arxiv.«2211.10788»
