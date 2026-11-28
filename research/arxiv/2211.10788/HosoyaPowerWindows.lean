import HosoyaSmoothTwists
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import LucasFibonacciIsolatedDivisors
import LucasFibonacciDiagonalUnion

/-! Prime multiplicities outside a fixed set detect powers of products on
translated windows of both Hosoya diagonals. -/

namespace Arxiv.«2211.10788».HosoyaPowerIsolation
open Finset Filter HosoyaNeighbor
open scoped Classical

/-- Exclude the chosen primes and every prime in a shift determinant. A remaining
prime divisor of this site cannot divide a second site within H steps. -/
def detectingPrimes (S : Finset ℕ) (H : ℕ) (s : HosoyaNeighbor) (n : ℕ) : Finset ℕ :=
  (s.value n).primeFactors \ (S ∪ (shiftDetProduct H).primeFactors)

private theorem value_pos (s : HosoyaNeighbor) (n : ℕ) : 0 < s.value n := by
  have hg := s.supportBounds.lower n
  by_contra! he
  rw [Nat.eq_zero_of_le_zero he] at hg
  have := Nat.one_le_two_pow (n:=n)
  omega

private theorem detects_only {S : Finset ℕ} {H i j p : ℕ} {s t : HosoyaNeighbor}
    (hp : p ∈ detectingPrimes S H s i) (hne : s ≠ t ∨ i ≠ j) (hg : Nat.dist i j ≤ H) :
    ¬ p ∣ t.value j := by
  obtain ⟨hval,hexc⟩ := mem_sdiff.mp hp
  obtain ⟨hpr,hdiv,_⟩ := Nat.mem_primeFactors.mp hval
  intro h
  exact hexc (mem_union_right _ (Nat.mem_primeFactors.mpr
    ⟨hpr,dvd_shiftDetProduct_of_shared hne hg hdiv h,(shiftDetProduct_pos _).ne'⟩))

/-- For fixed S and H, all sufficiently late sites on either diagonal have
coprime multiplicities among their prime divisors outside S that are exclusive
within H steps. The cutoff is common to both sides. -/
theorem eventual_detecting_gcd (h : QuadraticUnitBounds) (S : Finset ℕ) (H : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : HosoyaNeighbor,
      (detectingPrimes S H s n).gcd ((s.value n).factorization ·) = 1 := by
  obtain ⟨B,hB⟩ := outside_prime_for_every_exponent h (S ∪ (shiftDetProduct H).primeFactors)
  refine ⟨B^2, ?_⟩
  intro n hn s
  have hg := s.supportBounds.lower n
  have hpow := Nat.lt_two_pow_self (n:=n)
  have hv : B ≤ s.value n := by nlinarith
  have he := (either_diagonal_iff_pell _).mp (show
      (∃ j, s.value n=lucasFibonacciSum j) ∨ IsLowerNeighborValue (s.value n) by
    cases s
    · exact Or.inl ⟨n+2,rfl⟩
    · exact Or.inr (Or.inr ⟨n,rfl⟩))
  let g := (detectingPrimes S H s n).gcd ((s.value n).factorization ·)
  have hd (k : ℕ) (hk : 2 ≤ k) : ¬ k ∣ g := by
    obtain ⟨p,hp,hs,hnk⟩ := hB _ hv he k hk
    exact fun hg' => hnk (hg'.trans (Finset.gcd_dvd (mem_sdiff.mpr ⟨hp,hs⟩)))
  change g = 1
  by_contra! hn1
  by_cases hz : g = 0
  · exact hd 2 (by decide) (hz ▸ dvd_zero _)
  · exact hd g (by omega) dvd_rfl

#print axioms eventual_detecting_gcd

/-- The rational S-units, including both signs, as a subgroup membership condition. -/
def IsRationalSUnit (S : Finset ℕ) (q : ℚˣ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → padicValRat p (q : ℚ) = 0

/-- The diagonal value at a site, regarded as a nonzero rational. -/
def siteUnit (u : HosoyaNeighbor × ℕ) : ℚˣ :=
  Units.mk0 (u.1.value u.2 : ℚ) (by exact_mod_cast (value_pos ..).ne')

private theorem cast_finset_gcd (D : Finset ℕ) (f : ℕ → ℕ) :
    ((D.gcd f : ℕ) : ℤ) = D.gcd (fun p => (f p : ℤ)) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert a D ha ih =>
    rw [gcd_insert, gcd_insert, ← ih]
    rfl

private noncomputable def coordinate (D : Finset ℕ) (hD : ∀ p ∈ D, Nat.Prime p)
    (c : ℕ → ℤ) : ℚˣ →* Multiplicative ℤ where
  toFun q := Multiplicative.ofAdd (∑ p ∈ D, padicValRat p (q : ℚ) * c p)
  map_one' := by simp
  map_mul' a b := by
    change (∑ p ∈ D, padicValRat p ((a : ℚ)*(b : ℚ))*c p) =
      (∑ p ∈ D, padicValRat p (a : ℚ)*c p) + ∑ p ∈ D, padicValRat p (b : ℚ)*c p
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    let : Fact p.Prime := ⟨hD p hp⟩
    rw [padicValRat.mul (Units.ne_zero a) (Units.ne_zero b), add_mul]

/-- Each site in a sufficiently late fixed window has a rational valuation
coordinate taking value one there and zero on the other sites and on S-units.
Here integers in the range are written using the multiplicative group wrapper. -/
theorem eventual_window_coordinates (h : QuadraticUnitBounds) (S : Finset ℕ) (H : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ u : HosoyaNeighbor × ℕ, n ≤ u.2 → u.2 ≤ n+H →
      ∃ L : ℚˣ →* Multiplicative ℤ,
        (∀ q, IsRationalSUnit S q → L q = 1) ∧
        ∀ v : HosoyaNeighbor × ℕ, n ≤ v.2 → v.2 ≤ n+H →
          L (siteUnit v) = Multiplicative.ofAdd (if v=u then 1 else 0) := by
  obtain ⟨N,hN⟩ := eventual_detecting_gcd h S H
  refine ⟨N, ?_⟩
  intro n hn u hulo huhi
  let D := detectingPrimes S H u.1 u.2
  let f (p : ℕ) := (u.1.value u.2).factorization p
  have hp (p : ℕ) (hm : p ∈ D) := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hm).1
  obtain ⟨c,hc⟩ := D.gcd_eq_sum_mul (fun p => (f p : ℤ))
  rw [← cast_finset_gcd] at hc
  have hg : D.gcd f = 1 := hN u.2 (by omega) u.1
  rw [hg] at hc
  refine ⟨coordinate D hp c, ?_, ?_⟩
  · intro q hq
    change (∑ p ∈ D, padicValRat p (q : ℚ)*c p)=0
    refine sum_eq_zero fun p hm => ?_
    rw [hq p (hp p hm) (fun hh => (mem_sdiff.mp hm).2 (mem_union_left _ hh)), zero_mul]
  · intro v hvlo hvhi
    change (∑ p ∈ D, padicValRat p (v.1.value v.2 : ℚ)*c p) = if v=u then 1 else 0
    by_cases he : v=u
    · subst v
      rw [if_pos rfl, ← show ∑ p ∈ D, (f p : ℤ)*c p = 1 from hc.symm]
      apply sum_congr rfl
      intro p hm
      rw [padicValRat.of_nat, ← Nat.factorization_def _ (hp p hm)]
    · rw [if_neg he]
      refine sum_eq_zero fun p hm => ?_
      have hnsite : u.1 ≠ v.1 ∨ u.2 ≠ v.2 := by
        by_contra! hh
        exact he (Prod.ext hh.1 hh.2).symm
      have hnot := detects_only hm hnsite (by simp only [Nat.dist]; omega)
      rw [padicValRat.of_nat, ← Nat.factorization_def _ (hp p hm),
        Nat.factorization_eq_zero_of_not_dvd hnot]
      simp

#print axioms eventual_window_coordinates

/-- Simultaneous power test for all rational products in a fixed late window.
Exponents may be signed and an arbitrary rational S-unit may be removed.
At k = 0 the same equivalence gives multiplicative independence modulo S-units. -/
theorem eventual_window_power_iff (h : QuadraticUnitBounds) (S : Finset ℕ) (H : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ T : Finset (HosoyaNeighbor × ℕ),
      (∀ u ∈ T, n ≤ u.2 ∧ u.2 ≤ n+H) → ∀ (e : HosoyaNeighbor × ℕ → ℤ) (k : ℤ),
      (∃ a z : ℚˣ, IsRationalSUnit S a ∧ (∏ u ∈ T, siteUnit u ^ e u) = a*z^k) ↔
        ∀ u ∈ T, k ∣ e u := by
  obtain ⟨N,hN⟩ := eventual_window_coordinates h S H
  refine ⟨N, ?_⟩
  intro n hn T hT e k
  constructor
  · rintro ⟨a,z,ha,he⟩ u hu
    obtain ⟨L,hS,hL⟩ := hN n hn u (hT u hu).1 (hT u hu).2
    have hx := congrArg (fun q : ℚˣ => L q) he
    change L (∏ v ∈ T, siteUnit v ^ e v) = L (a*z^k) at hx
    rw [map_prod,map_mul,map_zpow,hS a ha,one_mul] at hx
    have hother (v : HosoyaNeighbor × ℕ) (hv : v ∈ T) (hne : v ≠ u) :
        L (siteUnit v ^ e v) = 1 := by
      rw [map_zpow, hL v (hT v hv).1 (hT v hv).2, if_neg hne]
      exact one_zpow _
    rw [prod_eq_single_of_mem u hu hother, map_zpow, hL u (hT u hu).1 (hT u hu).2,
      if_pos rfl] at hx
    have heq := congrArg Multiplicative.toAdd hx
    refine ⟨(L z).toAdd, ?_⟩
    simpa [toAdd_zpow, zsmul_eq_mul] using heq
  · intro he
    refine ⟨1, ∏ u ∈ T, siteUnit u ^ (e u/k), ?_, ?_⟩
    · intro p _ _
      simp
    · rw [one_mul, ← Finset.prod_zpow]
      apply prod_congr rfl
      intro u hu
      rw [← zpow_mul, Int.ediv_mul_cancel (he u hu)]

#print axioms eventual_window_power_iff

/-- Both the window width and the excluded small-prime cutoff can tend to
infinity along all starts. The argument gives no rate for this function. -/
theorem growing_window_power_iff (h : QuadraticUnitBounds) (S : Finset ℕ) :
    ∃ R : ℕ → ℕ, Monotone R ∧ Filter.Tendsto R Filter.atTop Filter.atTop ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ T : Finset (HosoyaNeighbor × ℕ),
      (∀ u ∈ T, n ≤ u.2 ∧ u.2 ≤ n+R n) → ∀ (e : HosoyaNeighbor × ℕ → ℤ) (k : ℤ),
      (∃ a z : ℚˣ, IsRationalSUnit (S ∪ range (R n+1)) a ∧
        (∏ u ∈ T, siteUnit u ^ e u) = a*z^k) ↔ ∀ u ∈ T, k ∣ e u := by
  classical
  have hw (r : ℕ) := eventual_window_power_iff h (S ∪ range (r+1)) r
  choose B hB using hw
  let R (n : ℕ) := Nat.findGreatest (fun r => B r ≤ n) n
  refine ⟨R, ?_, ?_, ?_⟩
  · intro i j hij
    exact (Nat.findGreatest_mono_left (P := fun r => B r ≤ i)
      (Q := fun r => B r ≤ j) (fun _ hr => hr.trans hij) i).trans
      (Nat.findGreatest_mono_right _ hij)
  · apply Filter.tendsto_atTop.mpr
    intro r
    filter_upwards [Filter.eventually_ge_atTop (max r (B r))] with n hn
    exact Nat.le_findGreatest (P := fun j => B j ≤ n) (by omega : r ≤ n) (by omega)
  · filter_upwards [Filter.eventually_ge_atTop (B 0)] with n hn
    exact hB (R n) n (Nat.findGreatest_spec (P := fun r => B r ≤ n) (Nat.zero_le n) hn)

#print axioms growing_window_power_iff

end Arxiv.«2211.10788».HosoyaPowerIsolation
