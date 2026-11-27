import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Falling-factorial roots and the deficit in Erdős 478

Each distinct root gives a different index that repeats an earlier factorial.
A simultaneous splitting argument gives unbounded deficits on primes where
five is a square. For quantitative results see Banks, Luca, Shparlinski and
Stichtenoth (https://journals.tubitak.gov.tr/math/vol29/iss2/6/) and Klurman
and Munsch (https://doi.org/10.5802/jtnb.974), §2.
-/

namespace Erdos478.FallingGap

open Finset Polynomial

variable (R : Type*) [CommRing R]

/-- A root is the upper endpoint of a factorial repetition of length `k`. -/
noncomputable def gap (k : ℕ) : R[X] := descPochhammer R k - 1

private theorem root_repeats {p k : ℕ} [Fact p.Prime] (hk : 2 ≤ k)
    {x : ZMod p} (hx : (gap (ZMod p) k).IsRoot x) :
    x.val ∈ Ico 1 p ∧ ∃ j ∈ Ico 1 p, j < x.val ∧ j.factorial % p = x.val.factorial % p := by
  have hval : (x.val.descFactorial k : ZMod p) = 1 := by
    rw [← descPochhammer_eval_eq_descFactorial, ZMod.natCast_zmod_val]
    simpa [gap, IsRoot.def, sub_eq_zero] using hx
  have hle : k ≤ x.val := by
    by_contra! h
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero] at hval
    exact zero_ne_one hval
  have hlt := x.val_lt
  have eqfac : (x.val - k).factorial % p = x.val.factorial % p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    have h := congrArg (fun n : ℕ ↦ (n : ZMod p)) (Nat.factorial_mul_descFactorial hle)
    simpa only [Nat.cast_mul, hval, mul_one] using h
  refine ⟨mem_Ico.mpr ⟨by omega, hlt⟩, ?_⟩
  rcases hle.eq_or_lt with he | he
  · refine ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩, by omega, ?_⟩
    simpa [he] using eqfac
  · exact ⟨x.val - k, mem_Ico.mpr ⟨by omega, by omega⟩, by omega, eqfac⟩

/-- A set of distinct gap endpoints can be deleted simultaneously, even when
its members witness different gap lengths or repeat the same factorial value. -/
theorem card_add_gap_endpoints {p : ℕ} [Fact p.Prime] (roots : Finset (ZMod p))
    (hroots : ∀ x ∈ roots, ∃ k, 2 ≤ k ∧ (gap (ZMod p) k).IsRoot x) :
    ((Ico 1 p).image (fun n ↦ n.factorial % p)).card +
      roots.card ≤ p - 1 := by
  classical
  let ends := roots.image ZMod.val
  let f := fun n : ℕ ↦ n.factorial % p
  have spec {i : ℕ} (hi : i ∈ ends) :
      i ∈ Ico 1 p ∧ ∃ j ∈ Ico 1 p, j < i ∧ f j = f i := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
    obtain ⟨k, hk, hr⟩ := hroots x hx
    exact root_repeats hk hr
  have cover : (Ico 1 p).image f ⊆ ((Ico 1 p) \ ends).image f := by
    intro y hy
    have h : ∃ i, i ∈ Ico 1 p ∧ f i = y := mem_image.mp hy
    obtain ⟨hi, he⟩ := Nat.find_spec h
    refine mem_image.mpr ⟨_, mem_sdiff.mpr ⟨hi, fun hhit ↦ ?_⟩, he⟩
    obtain ⟨j, hj, hlt, hjv⟩ := (spec hhit).2
    exact Nat.find_min h hlt ⟨hj, hjv.trans he⟩
  have hsub : ends ⊆ Ico 1 p := fun _ hi ↦ (spec hi).1
  have hc := (card_le_card cover).trans card_image_le
  have hr := card_le_card hsub
  have he : ends.card = roots.card := card_image_of_injective _ (ZMod.val_injective p)
  rw [card_sdiff_of_subset hsub, Nat.card_Ico] at hc
  rw [Nat.card_Ico] at hr
  change ((Ico 1 p).image f).card + roots.card ≤ p - 1
  omega

/-- Every distinct root of the falling-factorial polynomial counts separately,
even if witnesses from different roots have the same factorial value. -/
theorem card_add_gap_roots {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) :
    ((Ico 1 p).image (fun n ↦ n.factorial % p)).card +
      (gap (ZMod p) k).roots.toFinset.card ≤ p - 1 :=
  card_add_gap_endpoints _ fun _ hx ↦
    ⟨k, hk, isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)⟩

/-- At a prime of separable complete splitting, a gap of length `k` forces
at least `k + 1` missing residues. -/
theorem card_add_of_splits {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k)
    (hs : (gap (ZMod p) k).Splits) (hd : (gap (ZMod p) k).Separable) :
    ((Ico 1 p).image (fun n ↦ n.factorial % p)).card + k ≤ p - 1 := by
  have h := card_add_gap_roots k hk (p := p)
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hd), ← hs.natDegree_eq_card_roots] at h
  simpa only [gap, ← C_1, natDegree_sub_C, descPochhammer_natDegree] using h

/-- Schur's argument: a nonconstant integer polynomial has a root modulo some
prime above any prescribed cutoff. -/
private theorem large_prime_root (f : ℤ[X]) (hf : f.natDegree ≠ 0) (N : ℕ) :
    ∃ p > N, p.Prime ∧ ∃ x : ZMod p, (f.map (Int.castRingHom (ZMod p))).IsRoot x := by
  have hco := (Filter.tendstoCofinite_iff _).mp (f.tendstoCofinite_of_natDegree_ne_zero hf)
  obtain ⟨a, ha⟩ := (hco.eventually (Filter.eventually_cofinite_ne 0)).exists
  let t := f.eval a
  let m : ℤ := t * N.factorial
  have hm : m ≠ 0 := mul_ne_zero ha (by exact_mod_cast Nat.factorial_ne_zero N)
  let line (b : ℤ) := a + m * b
  have hinj : Function.Injective line := fun _ _ he ↦
    mul_left_cancel₀ hm (add_left_cancel he)
  have hline := hco.comp hinj.tendsto_cofinite
  obtain ⟨b, hplus, hminus⟩ := ((hline.eventually (Filter.eventually_cofinite_ne t)).and
    (hline.eventually (Filter.eventually_cofinite_ne (-t)))).exists
  obtain ⟨v, hv⟩ := sub_dvd_eval_sub (line b) a f
  let q : ℤ := 1 + (N.factorial : ℤ) * b * v
  have heval : f.eval (line b) = t * q := by
    change f.eval (line b) - t = (a + t * N.factorial * b - a) * v at hv
    dsimp only [q]
    linear_combination hv
  have hq : q.natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_natAbs_iff.mp (show q.natAbs = (1 : ℤ).natAbs from h) with h | h
    · exact hplus (by simpa [h] using heval)
    · exact hminus (by simpa [h] using heval)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq
  let : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) = 0 := (CharP.intCast_eq_zero_iff _ p q).mpr
    (Int.ofNat_dvd_left.mpr hpd)
  refine ⟨p, ?_, hp, (line b : ℤ), ?_⟩
  · by_contra! hpN
    have hfac := (ZMod.natCast_eq_zero_iff N.factorial p).mpr (Nat.dvd_factorial hp.pos hpN)
    simp [q, hfac] at hq0
  · change eval _ _ = 0
    rw [eval_map, eval₂_at_intCast]
    simp [heval, hq0]

open NumberField IntermediateField
open scoped nonZeroDivisors

/-- An integral primitive element is obtained by clearing the denominator of
a primitive element of the number field. -/
private theorem integral_generator (K : Type*) [Field K] [NumberField K] :
    ∃ θ : 𝓞 K, ℚ⟮(θ : K)⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization ℤ⁰ α
    (Algebra.IsIntegral.isIntegral (R := ℚ) α)
  let θ : 𝓞 K := ⟨m • α, hm⟩
  refine ⟨θ, top_unique ?_⟩
  rw [← hα, adjoin_simple_le_iff]
  have hz : ((m : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (nonZeroDivisors.coe_ne_zero m)
  apply (ℚ⟮(θ : K)⟯.toSubalgebra.toSubmodule.smul_mem_iff hz).mp
  rw [Int.cast_smul_eq_zsmul]
  exact mem_adjoin_simple_self ℚ (θ : K)

/-- An integral primitive element generates an order of full rank. Its
additive index annihilates the quotient and belongs to the conductor. -/
private theorem exponent_pos {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (hθ : ℚ⟮(θ : K)⟯ = ⊤) : 0 < RingOfIntegers.exponent θ := by
  let A := Algebra.adjoin ℤ ({θ} : Set (𝓞 K))
  have hmin : (minpoly ℤ θ).natDegree = (minpoly ℚ (θ : K)).natDegree := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral,
      (minpoly.monic θ.isIntegral).natDegree_map]
  have hr : Module.finrank ℤ A = Module.finrank ℤ (𝓞 K) := by
    rw [RingOfIntegers.rank, (Algebra.adjoin.powerBasis' θ.isIntegral).finrank,
      Algebra.adjoin.powerBasis'_dim, hmin,
      ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := ℚ) (θ : K)),
      hθ, IntermediateField.finrank_top']
  let H := A.toSubmodule.toAddSubgroup
  let : Finite ((𝓞 K) ⧸ H) := Submodule.finiteQuotientOfFreeOfRankEq A.toSubmodule hr
  have hi : 0 < H.index := by rw [AddSubgroup.index_eq_card]; exact Nat.card_pos
  rw [RingOfIntegers.exponent_eq_sInf]
  apply (Nat.sInf_mem (s := {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ}) ?_).1
  refine ⟨H.index, hi, mem_conductor_iff.mpr fun x ↦ ?_⟩
  change (H.index : 𝓞 K) * x ∈ H
  simpa only [nsmul_eq_mul] using H.nsmul_index_mem x

/-- Arbitrarily large rational primes admit a degree-one specialization of
the entire ring of integers of a fixed number field. -/
private theorem large_prime_specialization (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    ∃ p > N, p.Prime ∧ Nonempty (𝓞 K →+* ZMod p) := by
  obtain ⟨θ, hθ⟩ := integral_generator K
  have hpos := exponent_pos θ hθ
  obtain ⟨p, hp, hprime, x, hx⟩ := large_prime_root (minpoly ℤ θ)
    (minpoly.natDegree_pos θ.isIntegral).ne' (max N (RingOfIntegers.exponent θ))
  let : Fact p.Prime := ⟨hprime⟩
  have hcop : ¬ p ∣ RingOfIntegers.exponent θ :=
    Nat.not_dvd_of_pos_of_lt hpos (lt_of_le_of_lt (le_max_right _ _) hp)
  let g := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hker : Ideal.span ({g} : Set (ZMod p)[X]) ≤ RingHom.ker (evalRingHom x) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  let ev := Ideal.Quotient.lift _ (evalRingHom x) (fun y hy ↦ hker hy)
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan hcop
  exact ⟨p, lt_of_le_of_lt (le_max_left _ _) hp, hprime,
    ⟨(ev.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _)⟩⟩

/-- A monic integer polynomial splits completely modulo arbitrarily large
primes: specialize the integers of its splitting field. -/
theorem arbitrarily_large_splitting_prime (f : ℤ[X]) (hf : f.Monic) (N : ℕ) :
    ∃ p > N, p.Prime ∧ (f.map (Int.castRingHom (ZMod p))).Splits := by
  let F := f.map (algebraMap ℤ ℚ)
  let K := F.SplittingField
  let : NumberField K := {}
  have hK : (f.map (algebraMap ℤ K)).Splits := by
    simpa only [F, Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
      (SplittingField.splits F)
  let g := f.map (algebraMap ℤ (𝓞 K))
  have hg : g.map (algebraMap (𝓞 K) K) = f.map (algebraMap ℤ K) := by
    rw [show g = f.map _ from rfl, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hgSplit : g.Splits := by
    apply Splits.of_splits_map_of_injective (IsFractionRing.injective (𝓞 K) K) (hg ▸ hK)
    intro a ha
    rw [hg] at ha
    have hai : IsIntegral ℤ a := ⟨f, hf, by
      simpa only [aeval_def, eval₂_eq_eval_map, IsRoot.def] using (isRoot_of_mem_roots ha)⟩
    exact ⟨⟨a, hai⟩, rfl⟩
  obtain ⟨p, hp, hprime, ⟨φ⟩⟩ := large_prime_specialization K N
  refine ⟨p, hp, hprime, ?_⟩
  have hs := hgSplit.map φ
  simpa only [g, Polynomial.map_map, RingHom.ext_int (φ.comp (algebraMap ℤ (𝓞 K)))
    (Int.castRingHom (ZMod p))] using hs

private theorem gap_degree [IsDomain R] {k : ℕ} (hk : 0 < k) :
    (gap R k).IsMonicOfDegree k := by
  have h : (descPochhammer R k).IsMonicOfDegree k :=
    ⟨descPochhammer_natDegree R k, monic_descPochhammer R k⟩
  simpa only [gap, sub_eq_add_neg] using h.add_right (q := -(1 : R[X])) (by simpa using hk)

private theorem gap_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (k : ℕ) :
    (gap A k).map φ = gap B k := by simp [gap]

/-- In its own prime characteristic the falling factorial is the polynomial
`X ^ k - X`: the monic polynomials have the same degree and every element of
the prime field is a root. -/
private theorem prime_gap_derivative (k : ℕ) [Fact k.Prime] :
    (gap (ZMod k) k).derivative = -1 := by
  have hk := (Fact.out : k.Prime).one_lt
  let f := descPochhammer (ZMod k) k
  let g := (X ^ k - X : (ZMod k)[X])
  have hf : f.IsMonicOfDegree k :=
    ⟨descPochhammer_natDegree _ k, monic_descPochhammer _ k⟩
  have hg : g.IsMonicOfDegree k := by
    simpa only [g, sub_eq_add_neg] using (isMonicOfDegree_X_pow (ZMod k) k).add_right
      (q := -X) (by simpa using hk)
  have hfg : f = g := by
    apply sub_eq_zero.mp
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f - g) (f := id) Function.injective_id
    · intro i
      have he : f.eval i = 0 := by
        rw [← ZMod.natCast_zmod_val i]
        exact descPochhammer_eval_coe_nat_of_lt i.val_lt
      simp [g, he, ZMod.pow_card]
    · simpa only [ZMod.card] using hf.natDegree_sub_lt (by omega) hg
  change (f - 1).derivative = -1
  rw [hfg]
  simp [g, derivative_X_pow]

/-- A nonzero integer certificate for separability follows by reduction in
characteristic `k`, where the derivative of the gap polynomial is `-1`. -/
private theorem gap_resultant_ne_zero (k : ℕ) [Fact k.Prime] :
    (gap ℤ k).resultant (gap ℤ k).derivative k k ≠ 0 := by
  let φ := Int.castRingHom (ZMod k)
  intro h
  have hm := congrArg φ h
  rw [← resultant_map_map, ← derivative_map, gap_map, prime_gap_derivative k] at hm
  have hmon := gap_degree (ZMod k) (Fact.out : k.Prime).pos
  have hc := hmon.monic.coeff_natDegree
  rw [hmon.natDegree_eq] at hc
  rw [show (-1 : (ZMod k)[X]) = C (-1) by simp, resultant_C_right, hc] at hm
  simp [φ] at hm

/-- Outside the prime divisors of the certificate, all gap roots are simple. -/
private theorem separable_of_large {k p : ℕ} [Fact k.Prime] [Fact p.Prime]
    (hp : ((gap ℤ k).resultant (gap ℤ k).derivative k k).natAbs < p) :
    (gap (ZMod p) k).Separable := by
  let f := gap ℤ k
  let D := f.resultant f.derivative k k
  let φ := Int.castRingHom (ZMod p)
  have hD : φ D ≠ 0 := fun hz ↦ Nat.not_dvd_of_pos_of_lt
    (Int.natAbs_pos.mpr (gap_resultant_ne_zero k)) hp
    (Int.ofNat_dvd_left.mp ((CharP.intCast_eq_zero_iff _ p D).mp hz))
  have hd : f.natDegree = k := (gap_degree ℤ (Fact.out : k.Prime).pos).natDegree_eq
  have hder : f.derivative.natDegree ≤ k := (natDegree_derivative_le f).trans (by omega)
  obtain ⟨u, v, _, _, h⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
    hd.le hder (Or.inl (Fact.out : k.Prime).ne_zero)
  have h' := congrArg (Polynomial.map φ) h
  change (f * u + f.derivative * v).map φ = (C D).map φ at h'
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map, f, gap_map] at h'
  refine ⟨C (φ D)⁻¹ * u.map φ, C (φ D)⁻¹ * v.map φ, ?_⟩
  calc
    _ = C (φ D)⁻¹ * (gap (ZMod p) k * u.map φ + (gap (ZMod p) k).derivative * v.map φ) := by ring
    _ = 1 := by rw [h', ← C_mul, inv_mul_cancel₀ hD, C_1]

/-- For each prime gap length there are arbitrarily large square-5 primes
where every gap root is simple and rational over the residue field. -/
theorem arbitrarily_large_split_gap (k : ℕ) [Fact k.Prime] (N : ℕ) :
    ∃ p > N, p.Prime ∧ IsSquare (5 : ZMod p) ∧
      (gap (ZMod p) k).Splits ∧ (gap (ZMod p) k).Separable := by
  let f := gap ℤ k
  let g := (X ^ 2 - C 5 : ℤ[X])
  let D := f.resultant f.derivative k k
  have hfm := (gap_degree ℤ (Fact.out : k.Prime).pos).monic
  have hgm : g.Monic := monic_X_pow_sub_C 5 (by decide : 2 ≠ 0)
  obtain ⟨p, hp, hprime, hs⟩ := arbitrarily_large_splitting_prime (f * g)
    (hfm.mul hgm) (max N D.natAbs)
  let : Fact p.Prime := ⟨hprime⟩
  let φ := Int.castRingHom (ZMod p)
  change ((f * g).map φ).Splits at hs
  rw [Polynomial.map_mul, splits_mul ((hfm.map φ).ne_zero) ((hgm.map φ).ne_zero)] at hs
  have hgmap : g.map φ = X ^ 2 - C (5 : ZMod p) := by
    rw [show g = X ^ 2 - C 5 from rfl, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      map_ofNat]
  have hsquare := hgmap ▸ hs.2
  obtain ⟨x, hx⟩ := hsquare.exists_eval_eq_zero (by
    apply degree_ne_of_natDegree_ne
    rw [natDegree_X_pow_sub_C]
    decide)
  refine ⟨p, lt_of_le_of_lt (le_max_left _ _) hp, hprime, ⟨x, ?_⟩, ?_,
    separable_of_large (lt_of_le_of_lt (le_max_right _ _) hp)⟩
  · rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero, pow_two] at hx
    exact hx.symm
  · simpa only [f, gap_map] using hs.1

/-- Within primes where five is a square, both the prime and its number of
missing factorial residues can exceed any prescribed cutoffs. -/
theorem arbitrarily_large_deficit (D N : ℕ) :
    ∃ p > N, p.Prime ∧ IsSquare (5 : ZMod p) ∧
      ((Ico 1 p).image (fun n ↦ n.factorial % p)).card + D < p := by
  obtain ⟨k, hk, hprime⟩ := Nat.exists_infinite_primes D
  let : Fact k.Prime := ⟨hprime⟩
  obtain ⟨p, hp, hpp, hsq, hs, hsep⟩ := arbitrarily_large_split_gap k N
  let : Fact p.Prime := ⟨hpp⟩
  have hcard := card_add_of_splits k hprime.two_le hs hsep
  exact ⟨p, hp, hpp, hsq, by have := hpp.pos; omega⟩

/-- On a strictly increasing sequence of square-5 primes the missing count
tends to infinity. -/
theorem exists_prime_subsequence :
    ∃ P : ℕ → ℕ, StrictMono P ∧ (∀ i, (P i).Prime ∧ IsSquare (5 : ZMod (P i))) ∧
      Filter.Tendsto (fun i ↦ P i - ((Ico 1 (P i)).image (fun n ↦ n.factorial % P i)).card)
        Filter.atTop Filter.atTop := by
  choose q hgt hprime hsq hcount using arbitrarily_large_deficit
  let P : ℕ → ℕ := Nat.rec (q 0 0) fun i prev ↦ q (i + 1) prev
  refine ⟨P, strictMono_nat_of_lt_succ (fun i ↦ hgt (i + 1) (P i)), ?_, ?_⟩
  · rintro (_ | i)
    · exact ⟨hprime 0 0, hsq 0 0⟩
    · exact ⟨hprime _ _, hsq _ _⟩
  · apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with i hi
    have h : ((Ico 1 (P i)).image (fun n ↦ n.factorial % P i)).card + i < P i := by
      cases i with
      | zero => exact hcount 0 0
      | succ i => exact hcount (i + 1) (P i)
    omega

#print axioms exists_prime_subsequence
#print axioms arbitrarily_large_split_gap
#print axioms arbitrarily_large_deficit
#print axioms arbitrarily_large_splitting_prime
#print axioms card_add_gap_roots
#print axioms card_add_gap_endpoints
#print axioms card_add_of_splits

end Erdos478.FallingGap
