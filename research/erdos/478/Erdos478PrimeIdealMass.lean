import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Harmonic mass of degree-one prime ideals

Kummer–Dedekind identifies the degree-one primes above a good rational prime
with the distinct roots of the reduced minimal polynomial. Counting ideals in
dyadic shells and bounding their finite Euler products gives a uniform leading
coefficient in a lower bound for the harmonic mass of degree-one primes.
-/

namespace Erdos478.MeanDeficit

open Polynomial NumberField RingOfIntegers Ideal

/-- Degree-one primes above a good rational prime correspond to the distinct
roots of the reduced minimal polynomial. -/
theorem degree_one_card_eq_roots {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K)
    {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ exponent θ) :
    Nat.card {P : (span {(p : ℤ)}).primesOver (𝓞 K) // (P.val).inertiaDeg ℤ = 1} =
      ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  classical
  let g := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hg : g ≠ 0 := ((minpoly.monic θ.isIntegral).map _).ne_zero
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let A := {P : (span {(p : ℤ)}).primesOver (𝓞 K) // P.val.inertiaDeg ℤ = 1}
  let factor (P : A) := (e P.val).val
  have hfactor (P : A) : (factor P).Monic ∧ factor P ∣ g :=
    ((Polynomial.mem_normalizedFactors_iff hg).mp (Multiset.mem_toFinset.mp (e P.val).property)).2
  have hlin (P : A) : factor P = X - C (-(factor P).coeff 0) := by
    have hd := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hp (e P.val).property
    change ((e.symm (e P.val)).val).inertiaDeg ℤ = (factor P).natDegree at hd
    rw [e.symm_apply_apply, P.property] at hd
    simpa using (hfactor P).1.eq_X_add_C hd.symm
  let r (P : A) : g.roots.toFinset := ⟨-(factor P).coeff 0, by
    rw [Multiset.mem_toFinset, mem_roots hg, ← dvd_iff_isRoot, ← hlin P]
    exact (hfactor P).2⟩
  have hi : Function.Injective r := by
    intro P Q h
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    change factor P = factor Q
    calc
      _ = _ := hlin P
      _ = _ := congrArg (fun z : ZMod p => X - C z) (congrArg Subtype.val h)
      _ = _ := (hlin Q).symm
  have hs : Function.Surjective r := by
    intro z
    have hz := (mem_roots hg).mp (Multiset.mem_toFinset.mp z.property)
    let v : monicFactorsMod θ p := ⟨X - C z.val, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff hg).mpr
        ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.mpr hz⟩)⟩
    have hdeg : ((e.symm v).val).inertiaDeg ℤ = 1 :=
      (NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
        hp v.property).trans (natDegree_X_sub_C _)
    refine ⟨⟨e.symm v, hdeg⟩, Subtype.ext ?_⟩
    change - ((e (e.symm v)).val.coeff 0) = z.val
    rw [e.apply_symm_apply]
    simp [v]
  exact (Nat.card_congr (Equiv.ofBijective r ⟨hi, hs⟩)).trans
    (by simp only [Nat.card_eq_fintype_card, Fintype.card_coe, g])

#print axioms degree_one_card_eq_roots

open Finset UniqueFactorizationMonoid nonZeroDivisors Filter Topology
variable {K : Type*} [Field K] [NumberField K]

noncomputable def idealsUpTo (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finset ((Ideal (𝓞 K))⁰) := (Ideal.finite_setOfPred_absNorm_le₀ n).toFinset

theorem mem_idealsUpTo (I : (Ideal (𝓞 K))⁰) (n : ℕ) :
    I ∈ idealsUpTo K n ↔ absNorm I.val ≤ n := Set.Finite.mem_toFinset _

/-- A finite Euler product majorizes the harmonic mass of any finite family
of nonzero ideals supported on its prime factors. -/
theorem ideal_euler_bound (T : Finset ((Ideal (𝓞 K))⁰)) (P : Finset (Ideal (𝓞 K)))
    (hs : ∀ I ∈ T, ∀ J ∈ normalizedFactors I.val, J ∈ P)
    (hP : ∀ J ∈ P, 1 < absNorm J) :
    ∑ I ∈ T, (absNorm I.val : ℝ)⁻¹ ≤ ∏ J ∈ P, (1 - (absNorm J : ℝ)⁻¹)⁻¹ := by
  classical
  let v (I : (Ideal (𝓞 K))⁰) (j : P) := (normalizedFactors I.val).count j.val
  let w (j : P) := (absNorm j.val : ℝ)⁻¹
  have hw (j : P) : 0 ≤ w j := by dsimp [w]; positivity
  have ht (j : P) : w j < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hP j j.property)
  have hprod (I : (Ideal (𝓞 K))⁰) (hI : I ∈ T) : (∏ j : P, j.val ^ v I j) = I.val := by
    rw [prod_coe_sort P (fun j => j ^ (normalizedFactors I.val).count j)]
    apply Eq.trans _ (Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I))
    rw [Finset.prod_multiset_count]
    apply (Finset.prod_subset _ _).symm
    · intro j hj
      exact hs I hI j (Multiset.mem_toFinset.mp hj)
    · intro j _ hj
      rw [Multiset.count_eq_zero.mpr (fun h => hj (Multiset.mem_toFinset.mpr h)), pow_zero]
  have hv : Set.InjOn v ↑T := by
    intro I hI J hJ he
    apply Subtype.ext
    exact (hprod I hI).symm.trans ((congrArg (fun a : P → ℕ => ∏ j, j.val ^ a j) he).trans (hprod J hJ))
  have hwprod (I : (Ideal (𝓞 K))⁰) (hI : I ∈ T) : ∏ j : P, w j ^ v I j = (absNorm I.val : ℝ)⁻¹ := by
    simpa [w, map_prod] using congrArg (fun J : Ideal (𝓞 K) => (absNorm J : ℝ)⁻¹) (hprod I hI)
  let S (j : P) := T.image fun I => v I j
  have hsub : T.image v ⊆ Fintype.piFinset S := by
    rintro _ h
    obtain ⟨I, hI, rfl⟩ := mem_image.mp h
    exact Fintype.mem_piFinset.mpr fun j => mem_image_of_mem _ hI
  calc
    ∑ I ∈ T, (absNorm I.val : ℝ)⁻¹ = ∑ I ∈ T, ∏ j : P, w j ^ v I j :=
      sum_congr rfl fun I hI => (hwprod I hI).symm
    _ = ∑ a ∈ T.image v, ∏ j, w j ^ a j := (sum_image (f := fun a : P → ℕ => ∏ j, w j ^ a j) hv).symm
    _ ≤ ∑ a ∈ Fintype.piFinset S, ∏ j, w j ^ a j :=
      sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => prod_nonneg fun j _ => pow_nonneg (hw j) _
    _ = ∏ j, ∑ k ∈ S j, w j ^ k := (prod_univ_sum S _).symm
    _ ≤ ∏ j, (1 - w j)⁻¹ := by
      apply prod_le_prod (fun j _ => sum_nonneg fun k _ => pow_nonneg (hw j) k)
      intro j _
      have h := hasSum_geometric_of_lt_one (hw j) (ht j)
      exact (h.summable.sum_le_tsum _ fun k _ => pow_nonneg (hw j) k).trans_eq h.tsum_eq
    _ = ∏ J ∈ P, (1 - (absNorm J : ℝ)⁻¹)⁻¹ := prod_coe_sort P (fun J => (1 - (absNorm J : ℝ)⁻¹)⁻¹)

#print axioms ideal_euler_bound

private noncomputable def idealMass (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℝ :=
  ∑ I ∈ idealsUpTo K n, (absNorm I.val : ℝ)⁻¹

/-- Each large dyadic shell of ideals carries a fixed positive harmonic mass.
The constant may depend on the field. -/
private theorem dyadic_mass_step (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      idealMass K (2 ^ n) + c ≤ idealMass K (2 ^ (n + 1)) := by
  classical
  let A (n : ℕ) := idealsUpTo K (2 ^ n)
  let r := dedekindZeta_residue K
  have hr : 0 < r := dedekindZeta_residue_pos K
  have lim : Tendsto (fun n : ℕ => ((A n).card : ℝ) / 2 ^ n) atTop (𝓝 r) := by
    apply ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).congr
    intro n
    dsimp only [Function.comp_apply]
    congr 2
    rw [← Nat.card_eq_finsetCard (A n)]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun I => by
      change ((absNorm I.val : ℝ) ≤ 2 ^ n) ↔ _
      rw [mem_idealsUpTo]
      exact_mod_cast Iff.rfl
  have low := lim.eventually_const_lt (show 3 * r / 4 < r by linarith)
  have high := lim.eventually_lt_const (show r < 5 * r / 4 by linarith)
  refine ⟨r / 8, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (low.and high)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have h₁ := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1))).mp (hN (n + 1) (by omega)).1
  have h₂ := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp (hN n hn).2
  have inc : A n ⊆ A (n + 1) := by
    intro I hI
    exact (mem_idealsUpTo I _).mpr (((mem_idealsUpTo I _).mp hI).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ n)))
  have hcard : r / 8 * 2 ^ (n + 1) ≤ ((A (n + 1) \ A n).card : ℝ) := by
    rw [card_sdiff_of_subset inc, Nat.cast_sub (card_le_card inc), pow_succ] at *
    linarith
  let S := A (n + 1) \ A n
  have hweight : r / 8 ≤ ∑ I ∈ S, (absNorm I.val : ℝ)⁻¹ := by
    calc
      r / 8 ≤ (S.card : ℝ) / 2 ^ (n + 1) := (le_div_iff₀ (by positivity)).mpr hcard
      _ = ∑ _I ∈ S, ((2 : ℝ) ^ (n + 1))⁻¹ := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply sum_le_sum
        intro I hI
        apply inv_anti₀ (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I))
        exact_mod_cast (mem_idealsUpTo I _).mp (mem_sdiff.mp hI).1
  have hm := sum_sdiff (f := fun I : (Ideal (𝓞 K))⁰ => (absNorm I.val : ℝ)⁻¹) inc
  change _ + r / 8 ≤ _
  unfold idealMass
  change _ + _ ≤ ∑ I ∈ A (n + 1), _
  rw [← hm]
  linarith

private theorem dyadic_ideal_mass (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * n ≤ idealMass K (2 ^ n) := by
  obtain ⟨a, ha, he⟩ := dyadic_mass_step K
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have grow (j : ℕ) : a * j ≤ idealMass K (2 ^ (N + j)) := by
    induction j with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, Nat.add_zero, idealMass]
      positivity
    | succ j ih =>
      have h := hN (N + j) (by omega)
      rw [Nat.cast_succ, mul_add, mul_one]
      exact (add_le_add ih (le_refl a)).trans h
  refine ⟨a / 2, by positivity, eventually_atTop.mpr ⟨2 * N, fun n hn => ?_⟩⟩
  have h := grow (n - N)
  rw [Nat.add_sub_of_le (by omega : N ≤ n), Nat.cast_sub (by omega : N ≤ n)] at h
  have hl : (2 : ℝ) * N ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hl)]

open IsDedekindDomain
attribute [local instance] Int.ideal_span_isMaximal_of_prime

noncomputable abbrev abovePrime (K : Type*) [Field K] [NumberField K] (p : ℕ) :=
  IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)

theorem mem_over {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 K)) :
    J ∈ abovePrime K p ↔ J ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by
  let : Fact p.Prime := ⟨hp⟩
  exact IsDedekindDomain.mem_primesOverFinset_iff (p := span {(p : ℤ)}) (by simp [hp.ne_zero]) _

theorem norm_over {p : ℕ} (hp : p.Prime) {J : Ideal (𝓞 K)} (hJ : J ∈ abovePrime K p) :
    absNorm J = p ^ J.inertiaDeg ℤ ∧ 0 < J.inertiaDeg ℤ := by
  obtain ⟨hJ₁, hJ₂⟩ := (mem_over hp J).mp hJ
  exact ⟨by simpa using (Ideal.natAbs_pow_inertiaDeg (p : ℤ) J).symm, J.inertiaDeg_pos ℤ⟩

private theorem one_lt_norm_over {p : ℕ} (hp : p.Prime) {J : Ideal (𝓞 K)} (hJ : J ∈ abovePrime K p) :
    1 < absNorm J := by
  obtain ⟨he, hf⟩ := norm_over hp hJ
  rw [he]
  exact Nat.one_lt_pow hf.ne' hp.one_lt

private theorem bound_over_card {p : ℕ} (hp : p.Prime) :
    (abovePrime K p).card ≤ Module.finrank ℚ K := by
  let : Fact p.Prime := ⟨hp⟩
  classical
  let P := span {(p : ℤ)}
  have he : ((abovePrime K p : Finset _) : Set _) = P.primesOver (𝓞 K) :=
    IsDedekindDomain.coe_primesOverFinset (p := P) (by simp [P, hp.ne_zero]) _
  let : Fintype (P.primesOver (𝓞 K)) := Fintype.ofFinite _
  have hcard : (abovePrime K p).card = Fintype.card (P.primesOver (𝓞 K)) :=
    (Fintype.card_coe _).symm.trans (Fintype.card_congr (Equiv.setCongr he))
  rw [hcard, ← RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank P, Fintype.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro J _
  have : J.val.IsPrime := J.property.1
  exact Nat.mul_pos (J.val.ramificationIdx_pos ℤ) (J.val.inertiaDeg_pos ℤ)

noncomputable def linearCount (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ := by
  classical
  exact ((abovePrime K p).filter fun J => J.inertiaDeg ℤ = 1).card

theorem over_disjoint (X : ℕ) :
    (↑(Nat.primesLE X) : Set ℕ).PairwiseDisjoint (abovePrime K) := by
  intro p hp q hq hn
  apply disjoint_left.mpr
  intro J hJ hJ'
  have h₁ := ((mem_over (Nat.mem_primesLE.mp hp).2 J).mp hJ).2
  have h₂ := ((mem_over (Nat.mem_primesLE.mp hq).2 J).mp hJ').2
  apply hn
  simpa using congrArg Ideal.absNorm (h₁.over.trans h₂.over.symm)

theorem primes_support_ideals (X : ℕ) {I : (Ideal (𝓞 K))⁰} (hI : I ∈ idealsUpTo K X)
    {J : Ideal (𝓞 K)} (hJ : J ∈ normalizedFactors I.val) :
    J ∈ (Nat.primesLE X).biUnion (abovePrime K) := by
  have hpr := prime_of_normalized_factor J hJ
  let : J.IsPrime := Ideal.isPrime_of_prime hpr
  let : NeZero J := ⟨hpr.ne_zero⟩
  let p := absNorm (J.under ℤ)
  have hp : p.Prime := Nat.absNorm_under_prime J
  have hd : p ∣ absNorm I.val :=
    (Int.absNorm_under_dvd_absNorm J).trans (map_dvd absNorm (dvd_of_mem_normalizedFactors hJ))
  have hle := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I) hd
  refine mem_biUnion.mpr ⟨p, Nat.mem_primesLE.mpr ⟨hle.trans ((mem_idealsUpTo I X).mp hI), hp⟩, ?_⟩
  exact (mem_over hp _).mpr ⟨inferInstance, Int.liesOver_span_absNorm J⟩

private theorem log_factor_le {x : ℝ} (hx : 2 ≤ x) :
    Real.log (1 - x⁻¹)⁻¹ ≤ x⁻¹ + 2 / x ^ 2 := by
  have h : 0 < 1 - x⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  apply (Real.log_le_sub_one_of_pos (inv_pos.mpr h)).trans
  have hpos : 0 < x := by linarith
  have h₁ : 0 < x - 1 := by linarith
  have he : 1 - x⁻¹ = (x - 1) / x := by field_simp
  rw [he, inv_div]
  calc
    x / (x - 1) - 1 = 1 / (x - 1) := by field_simp [h₁.ne']; ring
    _ ≤ (x + 2) / x ^ 2 := (div_le_div_iff₀ h₁ (sq_pos_of_pos hpos)).mpr (by nlinarith)
    _ = x⁻¹ + 2 / x ^ 2 := by field_simp

private theorem log_factor_coarse {x : ℝ} (hx : 2 ≤ x) :
    Real.log (1 - x⁻¹)⁻¹ ≤ 2 / x := by
  apply (log_factor_le hx).trans
  have hpos : 0 < x := by linarith
  field_simp
  nlinarith

private theorem sum_log_over (p : ℕ) (hp : p.Prime) :
    ∑ J ∈ abovePrime K p, Real.log (1 - (absNorm J : ℝ)⁻¹)⁻¹ ≤
      (linearCount K p : ℝ) / p + (Module.finrank ℚ K : ℝ) * (2 / (p : ℝ) ^ 2) := by
  classical
  have hprime : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let f (J : Ideal (𝓞 K)) : ℝ := if J.inertiaDeg ℤ = 1 then (p : ℝ)⁻¹ else 0
  have hlocal (J) (hJ : J ∈ abovePrime K p) : Real.log (1 - (absNorm J : ℝ)⁻¹)⁻¹ ≤ f J + 2 / (p : ℝ) ^ 2 := by
    obtain ⟨he, hf⟩ := norm_over hp hJ
    by_cases h : J.inertiaDeg ℤ = 1
    · rw [he, h, pow_one]
      simpa [f, h] using log_factor_le hprime
    · have hsq : p ^ 2 ≤ absNorm J := he ▸ Nat.pow_le_pow_right hp.pos (by omega)
      have hs : (p : ℝ) ^ 2 ≤ (absNorm J : ℝ) := by exact_mod_cast hsq
      have hle : (2 : ℝ) ≤ (absNorm J : ℝ) := by nlinarith
      simp only [f, if_neg h, zero_add]
      exact (log_factor_coarse hle).trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hs)
  apply (sum_le_sum hlocal).trans
  rw [sum_add_distrib]
  have hsum : ∑ J ∈ abovePrime K p, f J = (linearCount K p : ℝ) / p := by
    dsimp [f]
    rw [← sum_filter]
    simp [linearCount, div_eq_mul_inv]
  rw [hsum]
  gcongr
  simpa only [sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right
    (show ((abovePrime K p).card : ℝ) ≤ Module.finrank ℚ K by exact_mod_cast bound_over_card hp) (by positivity)

/-- A one-sided Mertens estimate for degree-one primes. The coefficient of
`log n` is independent of the field. The cutoff of the prime sum is `2^n`. -/
theorem linear_prime_mass (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, Real.log n ≤ C +
      ∑ p ∈ Nat.primesLE (2 ^ n), (linearCount K p : ℝ) / p := by
  classical
  obtain ⟨c, hc, hlarge⟩ := dyadic_ideal_mass K
  let d : ℝ := Module.finrank ℚ K
  let err := d * 2 * ∑' p : ℕ, ((p : ℝ) ^ 2)⁻¹
  refine ⟨err - Real.log c, ?_⟩
  filter_upwards [hlarge, eventually_ge_atTop 1] with n hn hn₀
  let X := 2 ^ n
  let P := (Nat.primesLE X).biUnion (abovePrime K)
  have hP (J) (hJ : J ∈ P) : 1 < absNorm J := by
    obtain ⟨p, hp, hJ⟩ := mem_biUnion.mp hJ
    exact one_lt_norm_over (Nat.mem_primesLE.mp hp).2 hJ
  have hem := ideal_euler_bound (idealsUpTo K X) P (fun _ hi _ hj => primes_support_ideals X hi hj) hP
  have h := Real.log_le_log (mul_pos hc (Nat.cast_pos.mpr hn₀)) (hn.trans hem)
  have hpne (J) (hJ : J ∈ P) : (1 - (absNorm J : ℝ)⁻¹)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hP J hJ))).ne'
  rw [Real.log_mul hc.ne' (by positivity), Real.log_prod hpne,
    Finset.sum_biUnion (s := Nat.primesLE X) (over_disjoint X)] at h
  have hu := sum_le_sum (s := Nat.primesLE X) (fun p hp => sum_log_over (K := K) p (Nat.mem_primesLE.mp hp).2)
  rw [sum_add_distrib] at hu
  have herr : ∑ p ∈ Nat.primesLE X, (Module.finrank ℚ K : ℝ) * (2 / (p : ℝ) ^ 2) ≤ err := by
    have hsq := (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).sum_le_tsum
      (Nat.primesLE X) (fun i _ => by positivity)
    simpa [err, d, mul_assoc, div_eq_mul_inv, Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hsq (show 0 ≤ d * 2 by dsimp [d]; positivity)
  change Real.log n ≤ err - Real.log c + ∑ p ∈ Nat.primesLE X, _
  linarith
#print axioms linear_prime_mass

theorem linearCount_eq_roots {p : ℕ} [Fact p.Prime] (θ : 𝓞 K) (hp : ¬ p ∣ exponent θ) :
    linearCount K p = ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  classical
  rw [← degree_one_card_eq_roots θ hp]
  let S := (abovePrime K p).filter fun J => J.inertiaDeg ℤ = 1
  let e : S ≃ {P : (span {(p : ℤ)}).primesOver (𝓞 K) // P.val.inertiaDeg ℤ = 1} :=
    { toFun := fun J => ⟨⟨J.val, (mem_over Fact.out _).mp (mem_filter.mp J.property).1⟩,
        (mem_filter.mp J.property).2⟩
      invFun := fun J => ⟨J.val.val, mem_filter.mpr
        ⟨(mem_over Fact.out _).mpr J.val.property, J.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_eq_finsetCard S).symm.trans (Nat.card_congr e)

theorem linearCount_le {p : ℕ} (hp : p.Prime) :
    linearCount K p ≤ Module.finrank ℚ K :=
  (Finset.card_filter_le _ _).trans (bound_over_card hp)

#print axioms linearCount_le
#print axioms linearCount_eq_roots

end Erdos478.MeanDeficit
