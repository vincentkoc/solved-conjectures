import Erdos478PrimeIdealMass
import Erdos478DisjointGapFamilies

/-!
# The harmonic mean of missing factorial residues

Each irreducible gap polynomial contributes a unit to the leading term of
its prime-weighted root count. Distinct gaps give distinct repeated endpoints
at every prime above a fixed resultant cutoff.
-/

namespace Erdos478.MeanDeficit

open Polynomial NumberField RingOfIntegers IntermediateField Filter Topology Finset

/-- Prime harmonic sum of a nonnegative integer statistic, with inclusive cutoff. -/
noncomputable def primeMass (a : ℕ → ℕ) (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, (a p : ℝ) / p

private theorem mass_transfer (a b : ℕ → ℕ) (B X : ℕ)
    (h : ∀ p > B, p.Prime → a p ≤ b p) :
    primeMass a X ≤ primeMass b X + primeMass a B := by
  classical
  unfold primeMass
  have hl (p) (hp : p ∈ Nat.primesLE X) :
      (a p : ℝ) / p ≤ (b p : ℝ) / p + (if p ≤ B then (a p : ℝ) / p else 0) := by
    split_ifs with hB
    · exact le_add_of_nonneg_left (by positivity)
    · rw [add_zero]
      gcongr
      exact h p (by omega) (Nat.mem_primesLE.mp hp).2
  apply (sum_le_sum hl).trans
  rw [sum_add_distrib, ← sum_filter]
  apply add_le_add (le_refl _)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨h₁, h₂⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨h₂,(Nat.mem_primesLE.mp h₁).2⟩
  · intros
    positivity

/-- Distinct roots at a prime, extended by zero to other natural numbers. -/
noncomputable def rootCount (f : ℤ[X]) (p : ℕ) : ℕ := by
  classical
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    exact (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card
  · exact 0

private theorem rootCount_prime (f : ℤ[X]) (p : ℕ) [hp : Fact p.Prime] :
    rootCount f p = (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  classical
  simp [rootCount, hp.out]

private theorem exists_root_generator (f : ℤ[X]) (hm : f.Monic) (hi : Irreducible (f.map (algebraMap ℤ ℚ))) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : 𝓞 K),
      minpoly ℤ θ = f ∧ ℚ⟮(θ : K)⟯ = ⊤ := by
  let g := f.map (algebraMap ℤ ℚ)
  let : Fact (Irreducible g) := ⟨hi⟩
  let K := AdjoinRoot g
  let pb := AdjoinRoot.powerBasis hi.ne_zero
  let : FiniteDimensional ℚ K := pb.finite
  let : NumberField K := {}
  let α : K := AdjoinRoot.root g
  have hr : aeval α g = 0 := by exact (AdjoinRoot.aeval_eq g).trans AdjoinRoot.mk_self
  have hz : aeval α f = 0 := by
    rw [Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℤ ℚ K).symm f α]
    exact hr
  let θ : 𝓞 K := ⟨α, ⟨f, hm, hz⟩⟩
  refine ⟨K, inferInstance, inferInstance, θ, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral]
    exact (minpoly.eq_of_irreducible_of_monic hi hr (hm.map _)).symm
  · apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra, IntermediateField.top_toSubalgebra]
    exact AdjoinRoot.adjoinRoot_eq_top

/-- A monic polynomial irreducible over the rationals has at least a unit
leading term in its prime harmonic mean root count. -/
theorem irreducible_root_mass (f : ℤ[X]) (hm : f.Monic)
    (hi : Irreducible (f.map (algebraMap ℤ ℚ))) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, Real.log n ≤ C + primeMass (rootCount f) (2 ^ n) := by
  obtain ⟨K,_,_, θ, hmin, hgen⟩ := exists_root_generator f hm hi
  obtain ⟨c, hc⟩ := linear_prime_mass K
  let B := exponent θ
  have he (p : ℕ) (hB : B < p) (hp : p.Prime) : linearCount K p ≤ rootCount f p := by
    let : Fact p.Prime := ⟨hp⟩
    rw [linearCount_eq_roots θ (Nat.not_dvd_of_pos_of_lt (FallingGap.exponent_pos θ hgen) hB),
      hmin, rootCount_prime]
  refine ⟨c + primeMass (linearCount K) B, ?_⟩
  filter_upwards [hc] with n hn
  change Real.log n ≤ c + primeMass (linearCount K) (2 ^ n) at hn
  linarith [mass_transfer _ _ B (2 ^ n) he]

#print axioms irreducible_root_mass

/-- The number of missing residues in the finite image from the pinned statement. -/
def deficit (p : ℕ) : ℕ := p - ((Ico 1 p).image (fun i ↦ i.factorial % p)).card

private noncomputable def gapCount (S : Finset ℕ) (p : ℕ) : ℕ :=
  ∑ k ∈ S, rootCount (descPochhammer ℤ k - 1) p

private theorem gap_mass_lower (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (S.card : ℝ) * Real.log n ≤ C + primeMass (gapCount S) (2 ^ n) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp [gapCount, primeMass]⟩
  | @insert k S hk ih =>
    have hpos : 0 < k := by have h := hS k (mem_insert_self _ _); omega
    have hm : (descPochhammer ℤ k - 1).Monic := by
      have h : (descPochhammer ℤ k).IsMonicOfDegree k :=
        ⟨descPochhammer_natDegree ℤ k, monic_descPochhammer ℤ k⟩
      simpa only [sub_eq_add_neg] using (h.add_right (q := -(1 : ℤ[X])) (by simpa using hpos)).monic
    obtain ⟨b, hb⟩ := irreducible_root_mass _ hm (by simpa using GapFamilies.irreducible_gap_rat hpos)
    obtain ⟨c, hc⟩ := ih fun i hi => hS i (mem_insert_of_mem hi)
    refine ⟨b + c, ?_⟩
    filter_upwards [hb, hc] with n hn hm
    have he : primeMass (gapCount (insert k S)) (2 ^ n) =
        primeMass (rootCount (descPochhammer ℤ k - 1)) (2 ^ n) + primeMass (gapCount S) (2 ^ n) := by
      simp [primeMass, gapCount, sum_insert hk, add_div, sum_add_distrib]
    rw [he, card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith

private theorem gap_le_deficit (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k) :
    ∃ B, ∀ p > B, p.Prime → gapCount S p ≤ deficit p := by
  let f := GapFamilies.family ℤ S
  refine ⟨(f.resultant f.derivative).natAbs, ?_⟩
  intro p hB hp
  let : Fact p.Prime := ⟨hp⟩
  have he := GapFamilies.card_add_sum_gap_roots S hS hB
  have hl : gapCount S p ≤ ∑ k ∈ S, (descPochhammer (ZMod p) k - 1).roots.card := by
    apply sum_le_sum
    intro k _
    rw [rootCount_prime]
    simpa using (Multiset.toFinset_card_le ((descPochhammer (ZMod p) k - 1).roots))
  unfold deficit
  omega

private theorem gap_le_sum (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    gapCount S p ≤ ∑ k ∈ S, k := by
  let : Fact p.Prime := ⟨hp⟩
  apply sum_le_sum
  intro k _
  rw [rootCount_prime]
  simp only [Polynomial.map_sub, descPochhammer_map, Polynomial.map_one]
  exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
    ((natDegree_sub_le _ _).trans (by simp [descPochhammer_natDegree])))

/-- At each fixed truncation determined by `L` gap lengths, the harmonic
sum of missing factorial residues has leading coefficient at least `L`. -/
theorem truncated_deficit_mass (L : ℕ) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (L : ℝ) * Real.log n ≤ C +
      primeMass (fun p => min (deficit p) (∑ k ∈ Ico 2 (L + 2), k)) (2 ^ n) := by
  let S := Ico 2 (L + 2)
  have hS (k) (hk : k ∈ S) := (mem_Ico.mp hk).1
  obtain ⟨C, hC⟩ := gap_mass_lower S hS
  obtain ⟨B, hB⟩ := gap_le_deficit S hS
  refine ⟨C + primeMass (gapCount S) B, ?_⟩
  filter_upwards [hC] with n hn
  have h := mass_transfer (gapCount S) (fun p => min (deficit p) (∑ k ∈ S, k)) B (2 ^ n)
    (fun p hp hprime => le_min (hB p hp hprime) (gap_le_sum S hprime))
  have he : S.card = L := by simp [S]
  rw [he] at hn
  change _ ≤ _ + primeMass (fun p => min (deficit p) (∑ k ∈ S, k)) (2 ^ n)
  linarith

#print axioms truncated_deficit_mass

private theorem primeMass_mono_cutoff (a : ℕ → ℕ) {x y : ℕ} (h : x ≤ y) :
    primeMass a x ≤ primeMass a y :=
  sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono h) (fun _ _ _ => by positivity)

private theorem primeMass_nonneg (a : ℕ → ℕ) (x : ℕ) : 0 ≤ primeMass a x :=
  sum_nonneg fun _ _ => by positivity

private theorem all_prime_mass_step (n : ℕ) (hn : 0 < n) :
    primeMass (fun _ => 1) (2 ^ (n + 1)) ≤ primeMass (fun _ => 1) (2 ^ n) + 4 / n := by
  classical
  let A := Nat.primesLE (2 ^ n)
  let B := Nat.primesLE (2 ^ (n + 1))
  have hAB : A ⊆ B := Nat.primesLE_mono (Nat.pow_le_pow_right (by decide) (by omega))
  let D := B \ A
  let t := (2 : ℝ) ^ n * (n * Real.log 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hloc (p) (hp : p ∈ D) : (1 : ℝ) / p ≤ Real.log p / t := by
    obtain ⟨hpB, hpA⟩ := mem_sdiff.mp hp
    have hpr := (Nat.mem_primesLE.mp hpB).2
    have hlt : 2 ^ n < p := by
      by_contra! h
      exact hpA (Nat.mem_primesLE.mpr ⟨h, hpr⟩)
    have hle : (2 : ℝ) ^ n ≤ p := by exact_mod_cast hlt.le
    have h₁ := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ n) hle
    rw [Real.log_pow] at h₁
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hpr.pos) ht, one_mul, mul_comm (Real.log _)]
    exact mul_le_mul hle h₁ (mul_nonneg (Nat.cast_nonneg _) hlog.le) (Nat.cast_nonneg _)
  have hsum : ∑ p ∈ D, (1 : ℝ) / p ≤ 4 / n := by
    apply (sum_le_sum hloc).trans
    rw [← sum_div]
    apply (div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg sdiff_subset
      (fun p hB _ => Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hB).2.one_le))) ht.le).trans
    change (∑ p ∈ Nat.primesLE _, Real.log p) / t ≤ _
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    apply (div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) ht.le).trans
    have hf : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [hf]
    dsimp [t]
    push_cast
    rw [pow_succ]
    apply le_of_eq
    field_simp
    ring
  have he := sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hAB
  simp only [primeMass, Nat.cast_one]
  change (∑ p ∈ B, (1 : ℝ) / p) ≤ (∑ p ∈ A, (1 : ℝ) / p) + 4 / n
  dsimp [D] at hsum
  linarith

private theorem all_prime_mass_le (n : ℕ) (hn : 0 < n) :
    primeMass (fun _ => 1) (2 ^ n) ≤ 5 + 4 * Real.log n := by
  have hb (k : ℕ) : primeMass (fun _ => 1) (2 ^ (k + 1)) ≤ 1 + 4 * (harmonic k : ℝ) := by
    induction k with
    | zero =>
      have he : Nat.primesLE 2 = {2} := by decide
      norm_num [primeMass, he]
    | succ k ih =>
      have h := all_prime_mass_step (k + 1) (by omega)
      rw [harmonic_succ]
      push_cast
      rw [div_eq_mul_inv] at h
      push_cast at h
      linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hc := harmonic_le_one_add_log (k + 1)
  have hm : (harmonic k : ℝ) ≤ (harmonic (k + 1) : ℝ) := by
    rw [harmonic_succ]
    push_cast
    exact le_add_of_nonneg_right (by positivity)
  push_cast at hc ⊢
  linarith [hb k]

/-- For every fixed target mean, a bounded truncation of the deficit already
reaches it at all sufficiently large cutoffs, with prime harmonic weights. -/
theorem relative_truncated_mass (L : ℕ) :
    ∀ᶠ X : ℕ in atTop, (L : ℝ) * primeMass (fun _ => 1) X ≤
      primeMass (fun p => min (deficit p) (∑ k ∈ Ico 2 (4 * L + 3), k)) X := by
  let m := 4 * L + 1
  let a (p : ℕ) := min (deficit p) (∑ k ∈ Ico 2 (m + 2), k)
  obtain ⟨C, hC⟩ := truncated_deficit_mass m
  have ht : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hC.and (ht.eventually_ge_atTop
    (C + L * (5 + 4 * Real.log 2)))).and (eventually_ge_atTop 1))
  apply eventually_atTop.mpr
  refine ⟨2 ^ N, fun X hX => ?_⟩
  let n := Nat.log 2 X
  have hXpos : X ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity : 0 < 2 ^ N) hX)
  have hNX : N ≤ n := (Nat.le_log_iff_pow_le (by decide) hXpos).mpr hX
  obtain ⟨⟨hm, hl⟩, hn⟩ := hN n hNX
  have hy := primeMass_mono_cutoff (fun _ => 1) (Nat.lt_pow_succ_log_self (by decide : 1 < 2) X).le
  have hu := hy.trans (all_prime_mass_le (n + 1) (by omega))
  have hz : Real.log (n + 1 : ℕ) ≤ Real.log n + Real.log 2 := by
    rw [← Real.log_mul (by positivity : (n : ℝ) ≠ 0) (by norm_num)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by omega : n + 1 ≤ n * 2)
  have hbase := primeMass_mono_cutoff a (Nat.pow_log_le_self 2 hXpos)
  change (L : ℝ) * primeMass (fun _ => 1) X ≤ primeMass a X
  change (m : ℝ) * Real.log n ≤ C + primeMass a (2 ^ n) at hm
  have hup : primeMass (fun _ => 1) X ≤ 5 + 4 * Real.log n + 4 * Real.log 2 := by linarith
  have scale := mul_le_mul_of_nonneg_left hup (Nat.cast_nonneg L)
  dsimp [m] at hm
  push_cast at hm
  linarith

/-- The untruncated prime-harmonic mean of the exact deficit tends to infinity. -/
theorem harmonic_mean_deficit :
    Tendsto (fun X : ℕ => primeMass deficit X / primeMass (fun _ => 1) X) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨L, hL⟩ := exists_nat_ge b
  filter_upwards [relative_truncated_mass L, eventually_ge_atTop 2] with X hX ht
  have hpos : 0 < primeMass (fun _ => 1) X := by
    have he : Nat.primesLE 2 = {2} := by decide
    have h : 0 < primeMass (fun _ => 1) 2 := by norm_num [primeMass, he]
    exact h.trans_le (primeMass_mono_cutoff _ ht)
  apply hL.trans
  apply (le_div_iff₀ hpos).mpr
  apply hX.trans
  apply sum_le_sum
  intro p _
  exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (Nat.cast_nonneg p)

#print axioms relative_truncated_mass
#print axioms harmonic_mean_deficit

/-- The indicator of a factorial image missing at least `D` residues. -/
def missesAtLeast (D p : ℕ) : ℕ := if D ≤ deficit p then 1 else 0

/-- For each threshold, the qualifying primes carry at least `1/(54D)` of
the total prime harmonic weight at every sufficiently large cutoff. -/
theorem harmonic_proportion (D : ℕ) (hD : 0 < D) :
    ∀ᶠ X : ℕ in atTop, primeMass (fun _ => 1) X ≤
      54 * D * primeMass (missesAtLeast D) X := by
  classical
  let M := ∑ k ∈ Ico 2 (4 * (2 * D) + 3), k
  have hcap : M ≤ 54 * D ^ 2 := by
    have h₁ := sum_range_add_sum_Ico (fun k : ℕ => k) (by omega : 2 ≤ 4 * (2 * D) + 3)
    rw [show (∑ i ∈ range 2, i) = 1 by decide] at h₁
    change 1 + M = _ at h₁
    have h₂ := sum_range_id_mul_two (4 * (2 * D) + 3)
    rw [show 4 * (2 * D) + 3 - 1 = 4 * (2 * D) + 2 by omega, ← h₁] at h₂
    have hsq := Nat.le_mul_self D
    nlinarith
  have hpt (p : ℕ) : min (deficit p) M ≤ D + M * missesAtLeast D p := by
    dsimp [missesAtLeast]
    split_ifs with h
    · simpa only [mul_one] using (min_le_right (deficit p) M).trans (Nat.le_add_left M D)
    · simpa only [mul_zero, add_zero] using (min_le_left (deficit p) M).trans (by omega : deficit p ≤ D)
  filter_upwards [relative_truncated_mass (2 * D)] with X hX
  let T := primeMass (fun _ => 1) X
  let W := primeMass (missesAtLeast D) X
  have hm : primeMass (fun p => min (deficit p) M) X ≤ D * T + M * W := by
    dsimp [primeMass, T, W]
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p _
    simp only [Nat.cast_one, mul_div_assoc', mul_one]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hpt p) (Nat.cast_nonneg p)
  change ((2 * D : ℕ) : ℝ) * T ≤ primeMass (fun p => min (deficit p) M) X at hX
  push_cast at hX
  have hb := mul_le_mul_of_nonneg_right (show (M : ℝ) ≤ 54 * (D:ℝ) ^ 2 by exact_mod_cast hcap)
    (primeMass_nonneg (missesAtLeast D) X)
  change T ≤ 54 * D * W
  apply le_of_mul_le_mul_left (a := (D:ℝ)) _ (Nat.cast_pos.mpr hD)
  change (M:ℝ) * W ≤ _ at hb
  linarith

#print axioms harmonic_proportion

private def primeCount (a : ℕ → ℕ) (X : ℕ) := ∑ p ∈ Nat.primesLE X, a p

private def nextPrimeValue (a : ℕ → ℕ) (n : ℕ) := if (n + 1).Prime then a (n + 1) else 0

private theorem primeCount_succ (a : ℕ → ℕ) (n : ℕ) :
    primeCount a (n + 1) = primeCount a n + nextPrimeValue a n := by
  by_cases h : (n + 1).Prime <;>
    simp [primeCount, nextPrimeValue, Nat.primesLE_succ, h, Nat.notMem_primesLE, add_comm]

private theorem primeMass_succ (a : ℕ → ℕ) (n : ℕ) :
    primeMass a (n + 1) = primeMass a n + (nextPrimeValue a n : ℝ) / (n + 1) := by
  by_cases h : (n + 1).Prime <;>
    simp [primeMass, nextPrimeValue, Nat.primesLE_succ, h, Nat.notMem_primesLE, add_comm]

/-- Partial summation transfers a uniform upper bound for counting weights
to the corresponding harmonic weights, with the same additive error. -/
private theorem harmonic_of_count_bound (a b : ℕ → ℕ) (m C : ℕ)
    (h : ∀ n, m * primeCount a n ≤ primeCount b n + C) (n : ℕ) :
    (m : ℝ) * primeMass a n ≤ primeMass b n + C := by
  let G (i : ℕ) : ℝ := primeCount b i + C - (m : ℝ) * primeCount a i
  let E (i : ℕ) : ℝ := primeMass b i + C - m * primeMass a i
  have hG (i) : 0 ≤ G i := sub_nonneg.mpr (by exact_mod_cast h i)
  have step (i) : E (i + 1) = E i + (G (i + 1) - G i) / (i + 1) := by
    simp only [E, G, primeCount_succ, primeMass_succ, Nat.cast_add]
    ring
  have bound (i : ℕ) : G i / (i + 1) ≤ E i := by
    induction i with
    | zero => simp [G, E, primeMass, primeCount]
    | succ i ih =>
      rw [step]
      push_cast
      calc
        G (i + 1) / (i + 1 + 1) ≤ G (i + 1) / (i + 1) :=
          div_le_div_of_nonneg_left (hG _) (by positivity) (by linarith)
        _ = G i / (i + 1) + (G (i + 1) - G i) / (i + 1) := by ring
        _ ≤ _ := add_le_add ih (le_refl _)
  exact sub_nonneg.mp ((div_nonneg (hG n) (by positivity)).trans (bound n))

private theorem all_prime_mass_tendsto :
    Tendsto (primeMass fun _ => 1) atTop atTop := by
  obtain ⟨C, hC⟩ := linear_prime_mass ℚ
  apply tendsto_atTop.mpr
  intro b
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (b + C)
  obtain ⟨n, hn, hb⟩ := (hC.and ht).exists
  have hl : primeMass (linearCount ℚ) (2 ^ n) ≤ primeMass (fun _ => 1) (2 ^ n) := by
    apply sum_le_sum
    intro p hp
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    exact_mod_cast (by simpa using linearCount_le (K := ℚ) (Nat.mem_primesLE.mp hp).2 :
      linearCount ℚ p ≤ 1)
  change Real.log n ≤ C + primeMass (linearCount ℚ) (2 ^ n) at hn
  change b + C ≤ Real.log n at hb
  filter_upwards [eventually_ge_atTop (2 ^ n)] with X hX
  exact (show b ≤ primeMass (fun _ => 1) (2 ^ n) by linarith).trans (primeMass_mono_cutoff _ hX)

/-- At arbitrarily large ordinary cutoffs, at least a fraction
`1/(54D+1)` of the primes miss at least `D` factorial residues. -/
theorem frequently_many_deficit_primes (D : ℕ) (hD : 0 < D) :
    ∃ᶠ X : ℕ in atTop, (Nat.primesLE X).card ≤
      (54 * D + 1) * ((Nat.primesLE X).filter fun p => D ≤ deficit p).card := by
  classical
  let a := missesAtLeast D
  let b : ℕ → ℕ := fun _ => 1
  let m := 54 * D + 1
  have cb (n) : primeCount b n = (Nat.primesLE n).card := by simp [primeCount, b]
  have ca (n) : primeCount a n = ((Nat.primesLE n).filter fun p => D ≤ deficit p).card := by
    simp only [primeCount, a, missesAtLeast, Finset.card_filter]
  by_contra hf
  rw [not_frequently] at hf
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  let C := m * primeCount a N
  have hc (n) : m * primeCount a n ≤ primeCount b n + C := by
    by_cases hn : N ≤ n
    · have h := hN n hn
      rw [← cb, ← ca, not_le] at h
      exact h.le.trans (Nat.le_add_right _ _)
    · have hmono : primeCount a n ≤ primeCount a N :=
        sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
      exact (Nat.mul_le_mul_left m hmono).trans (Nat.le_add_left _ _)
  have hlarge := all_prime_mass_tendsto.eventually_ge_atTop ((54 * D : ℝ) * C + 1)
  obtain ⟨n, hw, ht⟩ := ((harmonic_proportion D hD).and hlarge).exists
  have hu := harmonic_of_count_bound a b m C hc n
  change primeMass b n ≤ 54 * D * primeMass a n at hw
  change 54 * (D:ℝ) * C + 1 ≤ primeMass b n at ht
  dsimp [m] at hu
  push_cast at hu
  have bound : primeMass a n ≤ C := by linarith
  have := mul_le_mul_of_nonneg_left bound (show 0 ≤ 54 * (D:ℝ) by positivity)
  linarith

#print axioms frequently_many_deficit_primes

end Erdos478.MeanDeficit
