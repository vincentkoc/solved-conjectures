import Green33PrimeMoments
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! Higher power sums at an extremal prime cyclic modulus. -/

open Finset Green33Multiplicity Green33ReflectionRigidity
open scoped Pointwise

namespace Green33NewtonObstruction

/-- Newton's identities transfer additive restrictions on power-sum degrees
to the degree of the top elementary symmetric polynomial. -/
private lemma degree_in_submonoid {ι K : Type*} [Fintype ι] [Field K] (v : ι → K)
    (D : AddSubmonoid ℕ) (hv : ∀ a, v a ≠ 0)
    (hc : ∀ j, 0 < j → j ≤ Fintype.card ι → (j : K) ≠ 0)
    (hp : ∀ j, j ≤ Fintype.card ι → j ∉ D → ∑ a, v a ^ j = 0) :
    Fintype.card ι ∈ D := by
  classical
  let E (j : ℕ) := MvPolynomial.eval v (MvPolynomial.esymm ι K j)
  have hps (r : ℕ) : MvPolynomial.eval v (MvPolynomial.psum ι K r) = ∑ a, v a ^ r := by
    simp [MvPolynomial.psum]
  have he (r : ℕ) (hr : r ≤ Fintype.card ι) (hn : r ∉ D) : E r = 0 := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      have hpos : 0 < r := Nat.pos_of_ne_zero fun hz => hn (hz ▸ D.zero_mem)
      have hrec := congrArg (fun P => MvPolynomial.eval v P) (MvPolynomial.mul_esymm_eq_sum ι K r)
      simp only [map_mul, map_natCast, map_neg, map_one, map_pow, map_sum, hps] at hrec
      change (r : K) * E r = _ at hrec
      rw [sum_eq_zero, mul_zero] at hrec
      · exact (mul_eq_zero.mp hrec).resolve_left (hc r hpos hr)
      · rintro ⟨j,k⟩ ht
        obtain ⟨hjk,hj⟩ := mem_filter.mp ht
        have heq : j + k = r := mem_antidiagonal.mp hjk
        by_cases hjD : j ∈ D
        · have hkD : k ∉ D := fun hk => hn (heq ▸ D.add_mem hjD hk)
          simp [hp k (by omega) hkD]
        · have hjzero := ih j hj (by omega) hjD
          change _ * E j * _ = 0
          simp [hjzero]
  by_contra hn
  have hz := he _ le_rfl hn
  change MvPolynomial.eval v (MvPolynomial.esymm ι K (Fintype.card ι)) = 0 at hz
  rw [MvPolynomial.esymm, ← card_univ, powersetCard_self, sum_singleton] at hz
  simp only [map_prod, MvPolynomial.eval_X] at hz
  exact (prod_ne_zero_iff.mpr fun a _ => hv a) hz

/-- At exact equality, the basis size belongs to every additive submonoid
containing all resonant degrees up to that size. -/
theorem card_mem_of_resonant_degrees (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p))
    (hA : A + A = univ) (he : 2 * p = A.card ^ 2 + 2) (hlt : A.card < p - 1)
    (D : AddSubmonoid ℕ) (hD : ∀ r, 0 < r → r ≤ A.card →
      2 * (A.card : ZMod p) + 2 ^ r = 0 → r ∈ D) : A.card ∈ D := by
  classical
  obtain ⟨s, _, hd, hoff⟩ := extremal_profile A hA (by rwa [ZMod.card])
  let v (a : ZMod p) := 2 * a - s
  have hv (a : ZMod p) (ha : a ∈ A) : v a ≠ 0 := by
    intro h
    have ha' : a + a = s := by simpa [v, two_mul] using sub_eq_zero.mp h
    have hf : a ∈ A.filter (fun b => b + b = s) := mem_filter.mpr ⟨ha, ha'⟩
    exact (card_pos.mpr ⟨a, hf⟩).ne' hd
  let P (j : ℕ) := ∑ a ∈ A, v a ^ j
  have vanishes (r : ℕ) (hrk : r ≤ A.card) (hn : r ∉ D) : P r = 0 := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      have hr : 0 < r := Nat.pos_of_ne_zero fun hh => hn (hh ▸ D.zero_mem)
      have hz : ∀ j, 0 < j → j < r → P j * P (r - j) = 0 := by
        intro j hj hjr
        by_cases hjD : j ∈ D
        · have hsum : j + (r - j) = r := by omega
          have hsub : r - j ∉ D := fun hs => hn (hsum ▸ D.add_mem hjD hs)
          rw [ih _ (by omega) (by omega) hsub, mul_zero]
        · rw [ih _ hjr (by omega) hjD, zero_mul]
      have hs := Green33PrimeMoments.extremal_moment A s hoff r hr (hrk.trans_lt hlt)
      rw [show (∑ a ∈ A, ∑ b ∈ A, (2 * a - s + (2 * b - s)) ^ r) = 2 * A.card * P r from
        Green33PrimeMoments.pair_moment_endpoints A v r hr hz] at hs
      have hprod : (2 * (A.card : ZMod p) + 2 ^ r) * P r = 0 := by rwa [add_mul]
      exact (mul_eq_zero.mp hprod).resolve_left fun hc => hn (hD r hr hrk hc)
  have hc (j : ℕ) (hj : 0 < j) (hjk : j ≤ Fintype.card A) : (j : ZMod p) ≠ 0 := by
    rw [Fintype.card_coe] at hjk
    exact fun hz => (Nat.le_of_dvd hj ((ZMod.natCast_eq_zero_iff _ _).mp hz)).not_gt (by omega)
  have hp (j : ℕ) (hj : j ≤ Fintype.card A) (hn : j ∉ D) : ∑ a : A, v a ^ j = 0 := by
    rw [Fintype.card_coe] at hj
    rw [univ_eq_attach, sum_attach A (fun a => v a ^ j)]
    exact vanishes j hj hn
  simpa using degree_in_submonoid (fun a : A => v a) D (fun a => hv a a.2) hc hp

private abbrev K := ZMod 173203273

private lemma two_pow_mod (r t : ℕ) (h : 2 ^ r % 173203273 = t % 173203273) :
    (2 : K) ^ r = (t : K) := by
  simpa only [Nat.cast_pow, Nat.cast_two] using (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h

set_option exponentiation.threshold 4500 in
private lemma resonance_degrees (r : ℕ) (hr : (2 : K) ^ r = -37224) :
    ∃ b : ℕ, r = 1106 + 4418 * b := by
  have hpow : (2 : K) ^ 4418 = 1 := two_pow_mod 4418 1 (by decide)
  have hord : orderOf (2 : K) = 4418 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hpow
    intro t ht hd
    have hfac : t = 2 ∨ t = 47 := by
      rw [show 4418 = 2 * (47 * 47) by decide] at hd
      rcases ht.dvd_mul.mp hd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq ht (by decide)).mp h)
      · rcases ht.dvd_mul.mp h with h | h <;>
          exact Or.inr ((Nat.prime_dvd_prime_iff_eq ht (by decide)).mp h)
    rcases hfac with rfl | rfl
    · rw [show 4418 / 2 = 2209 by decide, two_pow_mod 2209 173203272 (by decide)]
      decide
    · rw [show 4418 / 47 = 94 by decide, two_pow_mod 94 107637743 (by decide)]
      decide
  have hf : IsOfFinOrder (2 : K) := isOfFinOrder_iff_pow_eq_one.mpr ⟨4418, by decide, hpow⟩
  have hmod := hf.pow_eq_pow_iff_modEq.mp
    (hr.trans ((show (-37224 : K) = 173166049 by decide).trans
      (two_pow_mod 1106 173166049 (by decide)).symm))
  rw [hord] at hmod
  refine ⟨r / 4418, ?_⟩
  change r % 4418 = 1106 % 4418 at hmod
  omega

/-- The first nonzero moment condition holds here, but the full Newton
condition excludes a basis of size 18612. -/
theorem obstruction_mod_173203273 :
    (4 : ZMod 173203273) ^ 552 = -9306 ∧
      ∀ A : Finset (ZMod 173203273), A + A = univ → 18613 ≤ A.card := by
  constructor
  · have h : (4 ^ 552 : ℕ) % 173203273 = 173193967 % 173203273 := by
      set_option exponentiation.threshold 600 in decide
    have he := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    simp only [Nat.cast_pow, Nat.cast_ofNat] at he
    exact he.trans (by decide)
  · intro A hA
    have : Fact (Nat.Prime 173203273) := ⟨by norm_num⟩
    have hb := order_bound A hA
    rw [ZMod.card] at hb
    by_contra! h
    have hk : A.card = 18612 := by
      by_contra! hh
      have := Nat.pow_le_pow_left (show A.card ≤ 18611 by omega) 2
      omega
    let D : AddSubmonoid ℕ := {
      carrier := {r | ∃ a b : ℕ, r = 1106 * a + 4418 * b}
      zero_mem' := ⟨0, 0, rfl⟩
      add_mem' := by
        rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        exact ⟨a + c, b + d, by omega⟩ }
    have hr (r : ℕ) (_ : 0 < r) (_ : r ≤ A.card)
        (hc : 2 * (A.card : K) + 2 ^ r = 0) : r ∈ D := by
      rw [hk] at hc
      have hc' : (2 : K) ^ r = -37224 := by linear_combination hc
      obtain ⟨b, hb'⟩ := resonance_degrees r hc'
      exact ⟨1, b, by omega⟩
    have he := card_mem_of_resonant_degrees 173203273 A hA (by rw [hk]; decide)
      (by rw [hk]; decide) D hr
    obtain ⟨a, b, hab⟩ := he
    rw [hk] at hab
    have hb4 : b ≤ 4 := by omega
    interval_cases b <;> omega

#print axioms card_mem_of_resonant_degrees
#print axioms obstruction_mod_173203273

end Green33NewtonObstruction
