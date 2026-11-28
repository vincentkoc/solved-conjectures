import Erdos478PrimeIdealMass

/-!
# The log-norm convolution for integral ideals

Count multiples of each prime ideal power in a norm cutoff. Summing their log
weights recovers the total log norm of the ideals in the cutoff.
-/

namespace Erdos478.IdealMertens
open NumberField Ideal Finset nonZeroDivisors Erdos478.MeanDeficit

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- Multiplication by a fixed nonzero ideal counts exactly its multiples in a norm cutoff. -/
theorem multiples_count (A : (Ideal (𝓞 K))⁰) (X : ℕ) :
    ((idealsUpTo K X).filter (fun I : (Ideal (𝓞 K))⁰ => A.val ∣ I.val)).card =
      (idealsUpTo K (X / absNorm A.val)).card := by
  classical
  symm
  apply card_bij (fun J _ => A * J)
  · intro J hJ
    apply mem_filter.mpr
    refine ⟨(mem_idealsUpTo _ _).mpr ?_, ⟨J.val,rfl⟩⟩
    change absNorm (A.val * J.val) ≤ X
    rw [map_mul, mul_comm]
    exact (Nat.le_div_iff_mul_le (absNorm_pos_of_nonZeroDivisors A)).mp ((mem_idealsUpTo J _).mp hJ)
  · intro J _ J' _ he
    exact Subtype.ext (mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero A) (congrArg Subtype.val he))
  · intro I hI
    obtain ⟨hbox,hdiv⟩ := mem_filter.mp hI
    obtain ⟨B,hB⟩ := hdiv
    have hb : B ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.coe_ne_zero I (by simp [hB])
    let J : (Ideal (𝓞 K))⁰ := ⟨B,mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩
    refine ⟨J,(mem_idealsUpTo J _).mpr ?_,Subtype.ext hB.symm⟩
    apply (Nat.le_div_iff_mul_le (absNorm_pos_of_nonZeroDivisors A)).mpr
    have hN := (mem_idealsUpTo I _).mp hbox
    rwa [hB,map_mul,mul_comm] at hN

#print axioms multiples_count

open UniqueFactorizationMonoid

/-- Factorization computes the logarithm of the norm, including multiplicities. -/
theorem log_norm_factors (I : (Ideal (𝓞 K))⁰) :
    Real.log (absNorm I.val) =
      ((normalizedFactors I.val).map (fun P => Real.log (absNorm P))).sum := by
  classical
  let g : Ideal (𝓞 K) →* ℝ := (Nat.castRingHom ℝ).toMonoidHom.comp absNorm.toMonoidHom
  have hI : g I.val = ((normalizedFactors I.val).map g).prod := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  change Real.log (g I.val) = _
  rw [hI, Real.log_multiset_prod]
  · simp [g,Multiset.map_map]
  · intro y hy
    obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hy
    have hn := (irreducible_of_normalized_factor P hP).ne_zero
    change (absNorm P : ℝ) ≠ 0
    exact_mod_cast (absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hn))

#print axioms log_norm_factors

private theorem power_iff_count (I : (Ideal (𝓞 K))⁰) {P : Ideal (𝓞 K)}
    (hP : Irreducible P) (j : ℕ) :
    P ^ j ∣ I.val ↔ j ≤ (normalizedFactors I.val).count P := by
  classical
  rw [pow_dvd_iff_le_emultiplicity,emultiplicity_eq_count_normalizedFactors hP
    (nonZeroDivisors.coe_ne_zero I),normalize_eq]
  exact_mod_cast Iff.rfl

private theorem count_le_norm (I : (Ideal (𝓞 K))⁰) {P : Ideal (𝓞 K)} (hP : Irreducible P) :
    (normalizedFactors I.val).count P ≤ absNorm I.val := by
  classical
  let n := (normalizedFactors I.val).count P
  have hd := (power_iff_count I hP n).mpr le_rfl
  have hnorm := map_dvd absNorm hd
  rw [map_pow] at hnorm
  have hpos := absNorm_pos_of_nonZeroDivisors I
  have hP0 : 0 < absNorm P := absNorm_pos_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_iff_ne_zero.mpr hP.ne_zero)
  have hP1 : absNorm P ≠ 1 := fun h => hP.not_isUnit (Ideal.isUnit_iff.mpr (absNorm_eq_one_iff.mp h))
  calc
    n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ absNorm P ^ n := Nat.pow_le_pow_left (by omega) _
    _ ≤ absNorm I.val := Nat.le_of_dvd hpos hnorm

open Classical in
private theorem log_by_powers (I : (Ideal (𝓞 K))⁰) (X : ℕ) (hX : absNorm I.val ≤ X)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Irreducible P)
    (hsupp : ∀ P ∈ normalizedFactors I.val, P ∈ S) :
    Real.log (absNorm I.val) = ∑ P ∈ S, ∑ j ∈ Icc 1 X,
      if P ^ j ∣ I.val then Real.log (absNorm P) else 0 := by
  classical
  let f := normalizedFactors I.val
  rw [log_norm_factors, Finset.sum_multiset_map_count]
  change (∑ P ∈ f.toFinset, f.count P • Real.log (absNorm P)) = _
  rw [Finset.sum_subset (s₂ := S) (fun p hp => hsupp p (Multiset.mem_toFinset.mp hp))
    (fun p _ hp => by rw [Multiset.count_eq_zero.mpr (fun h => hp (Multiset.mem_toFinset.mpr h)),zero_smul])]
  apply sum_congr rfl
  intro P hP
  rw [← sum_filter]
  have eq : (Icc 1 X).filter (fun j => P^j ∣ I.val) = Icc 1 (f.count P) := by
    ext j
    simp only [mem_filter,mem_Icc,power_iff_count I (hS P hP) j]
    have hle : f.count P ≤ X := (count_le_norm I (hS P hP)).trans hX
    change (1 ≤ j ∧ j ≤ X) ∧ j ≤ f.count P ↔ 1 ≤ j ∧ j ≤ f.count P
    omega
  rw [eq,sum_const,Nat.card_Icc]
  simp

open Classical in
/-- Summing the logarithmic divisor identity expresses the total log norm as a finite
prime-power sum against the ideal counting function. -/
theorem log_norm_convolution (X : ℕ) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Irreducible P)
    (hcover : ∀ I ∈ idealsUpTo K X, ∀ P ∈ normalizedFactors I.val, P ∈ S) :
    ∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val) =
      ∑ P ∈ S, ∑ j ∈ Icc 1 X, ((idealsUpTo K (X / absNorm P ^ j)).card : ℝ) * Real.log (absNorm P) := by
  classical
  calc
    _ = ∑ I ∈ idealsUpTo K X, ∑ P ∈ S, ∑ j ∈ Icc 1 X,
        if P^j ∣ I.val then Real.log (absNorm P) else 0 := by
      apply sum_congr rfl
      intro I hI
      exact log_by_powers I X ((mem_idealsUpTo I X).mp hI) S hS (hcover I hI)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro P hP
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      let A : (Ideal (𝓞 K))⁰ := ⟨P^j, mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ (hS P hP).ne_zero)⟩
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      have hc := multiples_count A X
      change ((idealsUpTo K X).filter (fun I : (Ideal (𝓞 K))⁰ => P^j ∣ I.val)).card = (idealsUpTo K (X / absNorm (P^j))).card at hc
      rw [map_pow] at hc
      rw [hc]

#print axioms log_norm_convolution

open Filter Topology

private theorem box_mono {x y : ℕ} (h : x ≤ y) : idealsUpTo K x ⊆ idealsUpTo K y :=
  fun I hI => (mem_idealsUpTo I y).mpr (((mem_idealsUpTo I x).mp hI).trans h)

/-- Ideal counting at a real cutoff, for use at quotients of norms. -/
theorem ideal_count_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun y : ℝ => ((idealsUpTo K ⌊y⌋₊).card : ℝ) / y) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  apply (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  congr 2
  rw [← Nat.card_eq_finsetCard (idealsUpTo K ⌊y⌋₊)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I =>
    (Nat.le_floor_iff hy).symm.trans (mem_idealsUpTo I _).symm)

/-- An additive constant extends the relative ideal-counting estimate to every cutoff. -/
theorem ideal_count_error (K : Type*) [Field K] [NumberField K] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
      |((idealsUpTo K ⌊y⌋₊).card : ℝ) - dedekindZeta_residue K * y| ≤ ε * y + C := by
  let r := dedekindZeta_residue K
  have hr : 0 < r := dedekindZeta_residue_pos K
  obtain ⟨z,hz⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp (ideal_count_limit K)) ε hε)
  obtain ⟨N,hN⟩ := exists_nat_gt (max z 0)
  let C := ((idealsUpTo K N).card : ℝ) + r * N
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro y hy
  by_cases h : (N : ℝ) ≤ y
  · have hpos : 0 < y := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) h
    have hh := hz y (le_trans (le_max_left z 0) (hN.le.trans h))
    rw [Real.dist_eq] at hh
    change |((idealsUpTo K ⌊y⌋₊).card : ℝ) - r*y| ≤ _
    rw [show ((idealsUpTo K ⌊y⌋₊).card : ℝ) - r*y = (((idealsUpTo K ⌊y⌋₊).card : ℝ)/y-r)*y by field_simp,
      abs_mul, abs_of_pos hpos]
    exact (mul_le_mul_of_nonneg_right hh.le hy).trans (le_add_of_nonneg_right (by dsimp [C]; positivity))
  · have hcard : ((idealsUpTo K ⌊y⌋₊).card : ℝ) ≤ (idealsUpTo K N).card := by
      exact_mod_cast card_le_card (box_mono (Nat.floor_le_of_le (le_of_not_ge h)))
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_ge h) hr.le
    apply abs_le.mpr
    change _ ≤ _ - r*y ∧ _ - r*y ≤ _
    dsimp [C]
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (idealsUpTo K ⌊y⌋₊).card,
      mul_nonneg hε.le hy, mul_nonneg hr.le hy, Nat.cast_nonneg (α := ℝ) (idealsUpTo K N).card]

private theorem count_upper (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 1 ≤ j → ((idealsUpTo K j).card : ℝ) ≤ C * j := by
  obtain ⟨C,hC,h⟩ := ideal_count_error K (by norm_num : (0:ℝ)<1)
  have hr := (dedekindZeta_residue_pos K).le
  refine ⟨1+dedekindZeta_residue K+C,by positivity,?_⟩
  intro j hj
  have hh := (abs_le.mp (h j (Nat.cast_nonneg _))).2
  rw [Nat.floor_natCast,one_mul] at hh
  have h1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  nlinarith [mul_nonneg hC (sub_nonneg.mpr h1)]

theorem count_le_linear (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y → ((idealsUpTo K ⌊y⌋₊).card : ℝ) ≤ C*y := by
  classical
  obtain ⟨C,hC,h⟩ := count_upper K
  refine ⟨C,hC,fun y hy => ?_⟩
  by_cases h0 : ⌊y⌋₊ = 0
  · have hem : idealsUpTo K 0 = ∅ := eq_empty_iff_forall_notMem.mpr fun I hi =>
      (absNorm_pos_of_nonZeroDivisors I).not_ge ((mem_idealsUpTo I 0).mp hi)
    simp only [h0,hem,card_empty,Nat.cast_zero]
    exact mul_nonneg hC hy
  · exact (h _ (Nat.one_le_iff_ne_zero.mpr h0)).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hy) hC)

private theorem log_diff_bound {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ ∑ j ∈ Ico a b, (j:ℝ)⁻¹ := by
  have ha' : (0:ℝ)<a := by exact_mod_cast ha
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  calc
    _ = ∫ x in (a:ℝ)..b, x⁻¹ := by
      rw [integral_inv (by simp [Set.uIcc_of_le hab',not_le.mpr ha']),
        Real.log_div (ne_of_gt (ha'.trans_le hab')) ha'.ne']
    _ ≤ _ := (inv_antitoneOn_Icc_right ha').integral_le_sum_Ico hab

/-- The total log norm differs from the ideal count times log X by at most O(X). -/
theorem total_log_error (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ,
      0 ≤ ((idealsUpTo K X).card : ℝ) * Real.log X - ∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val) ∧
      ((idealsUpTo K X).card : ℝ) * Real.log X - ∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val) ≤ C*X := by
  classical
  obtain ⟨C,hC,h⟩ := count_upper K
  refine ⟨C,hC,fun X => ?_⟩
  rw [← nsmul_eq_mul,← sum_const,← sum_sub_distrib]
  constructor
  · apply sum_nonneg
    intro I hI
    apply sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast absNorm_pos_of_nonZeroDivisors I) ?_)
    exact_mod_cast (mem_idealsUpTo I X).mp hI
  · calc
      _ ≤ ∑ I ∈ idealsUpTo K X, ∑ j ∈ range X, if absNorm I.val ≤ j then (j:ℝ)⁻¹ else 0 := by
        apply sum_le_sum
        intro I hI
        have he : (range X).filter (fun j => absNorm I.val ≤ j) = Ico (absNorm I.val) X := by
          ext j
          simp [and_comm]
        rw [← sum_filter,he]
        exact log_diff_bound (absNorm_pos_of_nonZeroDivisors I) ((mem_idealsUpTo I X).mp hI)
      _ = ∑ j ∈ range X, ((idealsUpTo K j).card : ℝ) * (j:ℝ)⁻¹ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro j hj
        have he : (idealsUpTo K X).filter (fun I : (Ideal (𝓞 K))⁰ => absNorm I.val ≤ j) = idealsUpTo K j := by
          ext I
          simp only [mem_filter,mem_idealsUpTo]
          have hj' := mem_range.mp hj
          omega
        rw [← sum_filter,he,sum_const,nsmul_eq_mul]
      _ ≤ ∑ _j ∈ range X, C := by
        apply sum_le_sum
        intro j _
        by_cases hj : j = 0
        · simpa [hj] using hC
        · rw [← div_eq_mul_inv,div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj))]
          exact h j (Nat.one_le_iff_ne_zero.mpr hj)
      _ = C*X := by simp [mul_comm]

/-- The coefficient of X log X in the summatory log norm is the residue of the Dedekind zeta function. -/
theorem total_log_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun X : ℕ => (∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val)) /
      ((X:ℝ) * Real.log X)) atTop (𝓝 (dedekindZeta_residue K)) := by
  obtain ⟨C,_,h⟩ := total_log_error K
  have hcount := (ideal_count_limit K).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def,Nat.floor_natCast] at hcount
  have hzero : Tendsto (fun X : ℕ => C / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlo : Tendsto (fun X : ℕ => ((idealsUpTo K X).card : ℝ) / X - C / Real.log X) atTop
      (𝓝 (dedekindZeta_residue K)) := by simpa using hcount.sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hcount
  all_goals
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hx : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
    have hl : 0<Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1<X))
    obtain ⟨h₁,h₂⟩ := h X
    field_simp
    nlinarith

#print axioms ideal_count_limit
#print axioms ideal_count_error
#print axioms count_le_linear
#print axioms total_log_error
#print axioms total_log_limit

end Erdos478.IdealMertens
