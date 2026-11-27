import Erdos478UnboundedDeficit
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Simultaneous falling-factorial gaps

Distinct gap lengths give coprime characteristic-zero polynomials. This
prevents a shared factorial endpoint outside the primes dividing a resultant.
See Klurman and Munsch, https://doi.org/10.5802/jtnb.974, §2.
-/

namespace Erdos478.GapFamilies

open Polynomial Finset

private theorem gap_monic_degree (R : Type*) [CommRing R] [IsDomain R] {k : ℕ} (hk : 0 < k) :
    (descPochhammer R k - 1).IsMonicOfDegree k := by
  have h : (descPochhammer R k).IsMonicOfDegree k :=
    ⟨descPochhammer_natDegree R k, monic_descPochhammer R k⟩
  simpa only [sub_eq_add_neg] using h.add_right (q := -(1 : R[X])) (by simpa using hk)

/-- Schur's factorization argument for a falling-factorial gap of any positive length. -/
theorem irreducible_gap_int {k : ℕ} (hk : 0 < k) :
    Irreducible (descPochhammer ℤ k - 1) := by
  have hm := gap_monic_degree ℤ hk
  apply hm.monic.irreducible_iff_natDegree.mpr
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hd := hm.natDegree_eq
    rw [h, natDegree_one] at hd
    omega
  intro f g hf hg hfg
  by_contra! hz
  have hdeg := congrArg natDegree hfg
  rw [natDegree_mul hf.ne_zero hg.ne_zero, hm.natDegree_eq] at hdeg
  have roots (i : Fin k) : (f + g).eval (i.val : ℤ) = 0 := by
    have he := congrArg (eval (i.val : ℤ)) hfg
    rw [eval_mul, eval_sub, descPochhammer_eval_coe_nat_of_lt i.isLt, eval_one, zero_sub] at he
    have hunit : IsUnit (f.eval (i.val : ℤ) * g.eval (i.val : ℤ)) := he ▸ isUnit_neg_one
    obtain ha | ha := Int.isUnit_iff.mp (isUnit_of_mul_isUnit_left hunit)
    all_goals rw [eval_add, ha] ; rw [ha] at he ; omega
  have hzero : f + g = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f + g)
    (f := fun i : Fin k ↦ (i.val : ℤ)) (by intro i j h; exact Fin.ext (Int.ofNat_inj.mp h)) roots
    (by rw [Fintype.card_fin]; exact (natDegree_add_le _ _).trans_lt (by omega))
  have hl := congrArg leadingCoeff (eq_neg_of_add_eq_zero_left hzero)
  rw [hf.leadingCoeff, leadingCoeff_neg, hg.leadingCoeff] at hl
  omega

theorem irreducible_gap_rat {k : ℕ} (hk : 0 < k) :
    Irreducible (descPochhammer ℚ k - 1) := by
  have h := ((gap_monic_degree ℤ hk).monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp (irreducible_gap_int hk)
  simpa using h

/-- Distinct gap lengths yield coprime polynomials over the rationals.
Their product is separable even when the lengths are composite. -/
theorem separable_gap_family (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) :
    (∏ k ∈ S, (descPochhammer ℚ k - 1)).Separable := by
  apply separable_prod'
  · intro i hi j hj hne
    have cop {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
        IsCoprime (descPochhammer ℚ a - 1) (descPochhammer ℚ b - 1) := by
      apply (irreducible_gap_rat ha).coprime_iff_not_dvd.mpr
      intro h
      have hle := natDegree_le_of_dvd h (gap_monic_degree ℚ hb).monic.ne_zero
      rw [(gap_monic_degree ℚ ha).natDegree_eq, (gap_monic_degree ℚ hb).natDegree_eq] at hle
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact (cop (hS j hj) (hS i hi) h).symm
    · exact cop (hS i hi) (hS j hj) h
  · intro k hk
    exact (irreducible_gap_rat (hS k hk)).separable

/-- A fixed integral resultant excludes every prime at which the reduction
of a separable characteristic-zero polynomial can become inseparable. -/
theorem separable_mod_above_resultant (f : ℤ[X]) (hdeg : f.natDegree ≠ 0)
    (hs : (f.map (Int.castRingHom ℚ)).Separable) {p : ℕ} [Fact p.Prime]
    (hp : (f.resultant f.derivative).natAbs < p) :
    (f.map (Int.castRingHom (ZMod p))).Separable := by
  let D := f.resultant f.derivative
  let ι := Int.castRingHom ℚ
  have hin : Function.Injective ι := Int.cast_injective
  have hn : D ≠ 0 := by
    intro h
    have h' := congrArg ι h
    dsimp only [D] at h'
    rw [← resultant_map_map, map_zero] at h'
    have hcop : IsCoprime (f.map ι) (f.derivative.map ι) := by
      rw [← derivative_map]
      exact hs
    apply resultant_ne_zero _ _ hcop
    simpa only [natDegree_map_eq_of_injective hin] using h'
  let φ := Int.castRingHom (ZMod p)
  have hd : φ D ≠ 0 := fun h ↦ Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hn) hp
    (Int.ofNat_dvd_left.mp ((CharP.intCast_eq_zero_iff _ p D).mp h))
  obtain ⟨u,v,_,_,huv⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
    le_rfl le_rfl (Or.inl hdeg)
  have hh := congrArg (Polynomial.map φ) huv
  change (f * u + f.derivative * v).map φ = (C D).map φ at hh
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at hh
  refine ⟨C (φ D)⁻¹ * u.map φ, C (φ D)⁻¹ * v.map φ, ?_⟩
  calc
    _ = C (φ D)⁻¹ * (f.map φ * u.map φ + (f.map φ).derivative * v.map φ) := by ring
    _ = 1 := by rw [hh, ← C_mul, inv_mul_cancel₀ hd, C_1]

/-- The product tests all upper endpoints for a finite collection of gap lengths. -/
noncomputable def family (R : Type*) [CommRing R] (S : Finset ℕ) : R[X] :=
  ∏ k ∈ S, (descPochhammer R k - 1)

private theorem map_family {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Finset ℕ) : (family A S).map φ = family B S := by
  simp [family, Polynomial.map_prod]

private theorem family_degree (R : Type*) [CommRing R] [IsDomain R]
    (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) :
    (family R S).IsMonicOfDegree (∑ k ∈ S, k) := by
  have hm (k) (hk : k ∈ S) := (gap_monic_degree R (hS k hk)).monic
  refine ⟨?_, monic_prod_of_monic _ _ hm⟩
  rw [family, natDegree_prod_of_monic _ _ hm]
  exact sum_congr rfl fun k hk ↦ (gap_monic_degree R (hS k hk)).natDegree_eq

private theorem family_separable_mod (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
    {p : ℕ} [Fact p.Prime]
    (hp : ((family ℤ S).resultant (family ℤ S).derivative).natAbs < p) :
    (family (ZMod p) S).Separable := by
  rcases S.eq_empty_or_nonempty with rfl | hn
  · simp [family, separable_one]
  have hdegree := (family_degree ℤ S hS).natDegree_eq
  have hpos := sum_pos hS hn
  have hrat : ((family ℤ S).map (Int.castRingHom ℚ)).Separable := by
    rw [map_family]
    exact separable_gap_family S hS
  rw [← map_family (Int.castRingHom (ZMod p))]
  exact separable_mod_above_resultant _ (by omega) hrat hp

private theorem card_add_family_roots {p : ℕ} [Fact p.Prime] (S : Finset ℕ)
    (hS : ∀ k ∈ S, 2 ≤ k) :
    ((Ico 1 p).image (fun n ↦ n.factorial % p)).card +
      (family (ZMod p) S).roots.toFinset.card ≤ p - 1 := by
  apply FallingGap.card_add_gap_endpoints
  intro x hx
  have h := (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx))
  change (family (ZMod p) S).eval x = 0 at h
  rw [family, eval_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨k, hk, he⟩ := h
  exact ⟨k, hS k hk, he⟩

/-- Above an explicit resultant cutoff, all gap-root counts add, even
without complete splitting. The sum counts roots with multiplicity. -/
theorem card_add_sum_gap_roots (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k)
    {p : ℕ} [Fact p.Prime]
    (hp : ((family ℤ S).resultant (family ℤ S).derivative).natAbs < p) :
    ((Ico 1 p).image (fun n ↦ n.factorial % p)).card +
      ∑ k ∈ S, (descPochhammer (ZMod p) k - 1).roots.card ≤ p - 1 := by
  have hpos (k) (hk : k ∈ S) : 0 < k := by have := hS k hk; omega
  have h := card_add_family_roots S hS (p := p)
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (family_separable_mod S hpos hp))] at h
  have hn := (family_degree (ZMod p) S hpos).monic.ne_zero
  rw [family, roots_prod _ _ hn, Multiset.card_bind] at h
  exact h

/-- Simultaneous complete splitting can additionally impose the complete
splitting of any prescribed monic integral polynomial. -/
theorem arbitrarily_large_split_family (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k)
    (g : ℤ[X]) (hg : g.Monic) (N : ℕ) :
    ∃ p > N, p.Prime ∧ (g.map (Int.castRingHom (ZMod p))).Splits ∧
      (family (ZMod p) S).Splits ∧ (family (ZMod p) S).Separable ∧
      ((Ico 1 p).image (fun n ↦ n.factorial % p)).card + ∑ k ∈ S, k ≤ p - 1 := by
  let f := family ℤ S
  have hpos (k) (hk : k ∈ S) : 0 < k := by have := hS k hk; omega
  have hm := (family_degree ℤ S hpos).monic
  let D := (f.resultant f.derivative).natAbs
  obtain ⟨p, hp, hprime, hs⟩ := FallingGap.arbitrarily_large_splitting_prime (f * g)
    (hm.mul hg) (max N D)
  let : Fact p.Prime := ⟨hprime⟩
  let φ := Int.castRingHom (ZMod p)
  rw [Polynomial.map_mul, splits_mul (hm.map φ).ne_zero (hg.map φ).ne_zero] at hs
  have hf : (family (ZMod p) S).Splits := map_family φ S ▸ hs.1
  have hd := family_separable_mod S hpos (lt_of_le_of_lt (le_max_right _ _) hp)
  have hc := card_add_family_roots S hS (p := p)
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hd), ← hf.natDegree_eq_card_roots,
    (family_degree (ZMod p) S hpos).natDegree_eq] at hc
  exact ⟨p, lt_of_le_of_lt (le_max_left _ _) hp, hprime, hs.2, hf, hd, hc⟩

/-- In every class 1 modulo a positive m there are arbitrarily large primes
with simultaneous splitting of all gap lengths 2,...,L+1 and at least
(L+2 choose 2) missing factorial residues, including zero. -/
theorem triangular_deficit_in_progression (L m N : ℕ) (hm : 0 < m) :
    ∃ p > N, p.Prime ∧ m ∣ p - 1 ∧
      (family (ZMod p) (Ico 2 (L + 2))).Splits ∧ (family (ZMod p) (Ico 2 (L + 2))).Separable ∧
      ((Ico 1 p).image (fun n ↦ n.factorial % p)).card + (L + 2).choose 2 ≤ p := by
  let S := Ico 2 (L + 2)
  obtain ⟨p, hp, hprime, hcycl, hs, hd, hc⟩ := arbitrarily_large_split_family S
    (fun _ hk ↦ (mem_Ico.mp hk).1) (cyclotomic m ℤ) (cyclotomic.monic m ℤ) (max N m)
  let : Fact p.Prime := ⟨hprime⟩
  have hmp := lt_of_le_of_lt (le_max_right N m) hp
  let : NeZero (m : ZMod p) := ⟨fun h ↦ Nat.not_dvd_of_pos_of_lt hm hmp
    ((CharP.cast_eq_zero_iff (ZMod p) p m).mp h)⟩
  rw [map_cyclotomic] at hcycl
  obtain ⟨z, hz⟩ := hcycl.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by
    rw [natDegree_cyclotomic]; exact (Nat.totient_pos.mpr hm).ne'))
  have hprim := isRoot_cyclotomic_iff.mp (show (cyclotomic m (ZMod p)).IsRoot z from hz)
  have hn : z ≠ 0 := by
    rintro rfl
    simpa [zero_pow hm.ne'] using hprim.pow_eq_one
  have hsum := sum_range_add_sum_Ico (fun k : ℕ ↦ k) (show 2 ≤ L + 2 by omega)
  rw [show (∑ i ∈ range 2, i) = 1 by decide, sum_range_id, ← Nat.choose_two_right] at hsum
  change _ + ∑ k ∈ Ico 2 (L + 2), k ≤ p - 1 at hc
  refine ⟨p, lt_of_le_of_lt (le_max_left _ _) hp, hprime, hprim.dvd_of_pow_eq_one _
    (ZMod.pow_card_sub_one_eq_one hn), hs, hd, ?_⟩
  have := hprime.pos
  omega

#print axioms triangular_deficit_in_progression
#print axioms card_add_sum_gap_roots
#print axioms arbitrarily_large_split_family
#print axioms irreducible_gap_int
#print axioms irreducible_gap_rat
#print axioms separable_gap_family
#print axioms separable_mod_above_resultant

end Erdos478.GapFamilies
