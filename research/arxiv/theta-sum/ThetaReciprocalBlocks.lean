import ThetaReciprocalFibers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.PSeries

/-! Square summability of the rational cutoff coefficients grouped by frequency denominator. -/

namespace Arxiv.«2501.03234».ThetaReciprocalBlocks

open Finset ThetaReciprocalFibers

/-- Weight of the odd common factors discarded on reducing v/u. -/
noncomputable def commonWeight (Y d : ℕ) : ℝ :=
  ∑ g ∈ (Icc 1 (Y/d)).filter (·%2=1), ((g : ℝ)^2)⁻¹

private noncomputable def zetaTwo : ℝ := ∑' g : ℕ, ((g : ℝ)^2)⁻¹

private lemma commonWeight_nonneg (Y d : ℕ) : 0 ≤ commonWeight Y d := by
  unfold commonWeight; positivity

private lemma commonWeight_le (Y d : ℕ) : commonWeight Y d ≤ zetaTwo :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).sum_le_tsum _ (by intros; positivity)

/-- A primitive odd numerator contributes a vector indexed by additive frequencies;
the vector is zero outside the odd coprime support. -/
noncomputable def numeratorVector (q m w : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  if H : m%2=1 ∧ q%2=1 ∧ w%2=1 ∧ w.Coprime (q*m) then
    let _ : NeZero (q*m) := ⟨(Nat.mul_pos (NeZero.pos q) (by omega)).ne'⟩
    WithLp.toLp 2 (reciprocalCoeff q m (ZMod.unitOfCoprime w H.2.2.2))
  else 0

private lemma numeratorVector_bound (q m w : ℕ) [NeZero q] :
    ‖numeratorVector q m w‖ ≤ m.divisors.card / (m : ℝ) := by
  unfold numeratorVector
  split_ifs with H
  · let : NeZero (q*m) := ⟨(Nat.mul_pos (NeZero.pos q) (by omega)).ne'⟩
    have he := reciprocalCoeff_energy H.1 H.2.1 (ZMod.unitOfCoprime w H.2.2.2)
    rw [EuclideanSpace.norm_eq,Real.sqrt_le_iff]
    exact ⟨by positivity,he⟩
  · rw [norm_zero]; positivity

/-- All primitive numerators at a fixed original denominator q*m, projected to q. -/
noncomputable def numeratorRow (q m : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  ∑ k ∈ range (q*m-1), (((k : ℝ)+1)⁻¹) • numeratorVector q m (k+1)

private lemma numeratorRow_bound (q m : ℕ) [NeZero q] :
    ‖numeratorRow q m‖ ≤ (harmonic (q*m) : ℝ) * (m.divisors.card / (m : ℝ)) := by
  unfold numeratorRow
  apply (norm_sum_le ..).trans
  have hr : (harmonic (q*m) : ℝ) = ∑ k ∈ range (q*m), ((k : ℝ)+1)⁻¹ := by simp [harmonic]
  rw [hr,sum_mul]
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le (q*m) 1)) (by intros; positivity))
  apply sum_le_sum; intro k _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (numeratorVector_bound ..) (by positivity)

/-- The entire weighted block at projected denominator q. Its primitive coordinates
are exactly the frequencies with reduced denominator q in the cutoff expansion. -/
noncomputable def weightedBlock (Y q : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  ∑ m ∈ Icc 1 (Y/q), (commonWeight Y (q*m) / ((q:ℝ)*m)) • numeratorRow q m

private lemma weightedBlock_finite_bound (Y q : ℕ) [NeZero q] :
    ‖weightedBlock Y q‖ ≤ (zetaTwo / q) *
      ∑ m ∈ Icc 1 (Y/q), (harmonic (q*m) : ℝ) * m.divisors.card / (m:ℝ)^2 := by
  unfold weightedBlock
  apply (norm_sum_le ..).trans
  rw [mul_sum]
  apply sum_le_sum; intro m hm
  have hm' : 0<(m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
  have hq' : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (commonWeight_nonneg ..) (by positivity))]
  apply (mul_le_mul (div_le_div_of_nonneg_right (commonWeight_le ..) (by positivity))
    (numeratorRow_bound q m) (norm_nonneg _) (div_nonneg ((commonWeight_nonneg ..).trans
      (commonWeight_le Y (q*m))) (by positivity))).trans
  apply le_of_eq; ring

private lemma divisors_card_sqrt (m : ℕ) : m.divisors.card ≤ 2*m.sqrt := by
  let A := m.divisors.filter (· ≤ m.sqrt)
  let B := m.divisors.filter (fun d => ¬d ≤ m.sqrt)
  have ha : A.card ≤ m.sqrt := by
    calc
      _ ≤ (Icc 1 m.sqrt).card := card_le_card (by
        intro d hd; have hh := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hh.1,hh.2⟩)
      _ = _ := by simp
  have hb : B.card ≤ (Icc 1 m.sqrt).card := by
    apply card_le_card_of_injOn (fun d => m/d)
    · intro d hd; obtain ⟨hm,hd'⟩ := mem_filter.mp hd
      have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hm)
      apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.divisor_le hm) (Nat.pos_of_mem_divisors hm),
        (Nat.le_sqrt_of_eq_mul he.symm).resolve_left hd'⟩
    · intro d hd e he hh
      have hd' := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      have he' := Nat.dvd_of_mem_divisors (mem_filter.mp he).1
      have hp := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
      have ht : 0 < m/d := Nat.div_pos (Nat.divisor_le (mem_filter.mp hd).1) hp
      change m/d = m/e at hh
      apply Nat.eq_of_mul_eq_mul_right ht
      rw [Nat.mul_div_cancel' hd',hh,Nat.mul_div_cancel' he']
  have he : A.card+B.card=m.divisors.card := card_filter_add_card_filter_not ..
  simp at hb; omega

private noncomputable def zetaFiveFourths : ℝ := ∑' m : ℕ, ((m : ℝ)^(5/4 : ℝ))⁻¹

private lemma harmonic_divisors {q m : ℕ} (hq : 0<q) (hm : 0 < m) :
    (harmonic (q*m) : ℝ)*m.divisors.card / (m:ℝ)^2 ≤
    10*(1+Real.log q)*((m:ℝ)^(5/4:ℝ))⁻¹ := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hm' : (1:ℝ)≤ m := by exact_mod_cast hm
  have hmp : 0<(m:ℝ) := by positivity
  have hqp : 0<(q:ℝ) := by positivity
  have hlog := Real.log_nonneg hq'
  have hquarter : 1 ≤ (m:ℝ)^(1/4:ℝ) := Real.one_le_rpow hm' (by norm_num)
  have hl := Real.log_natCast_le_rpow_div m (show (0:ℝ)<1/4 by norm_num)
  have hH : (harmonic (q*m) : ℝ) ≤ 5*(1+Real.log q)*(m:ℝ)^(1/4:ℝ) := by
    apply (harmonic_le_one_add_log _).trans
    rw [Nat.cast_mul,Real.log_mul hqp.ne' hmp.ne']
    nlinarith [mul_nonneg hlog (sub_nonneg.mpr hquarter)]
  have hs : (m.sqrt:ℝ) ≤ (m:ℝ)^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' m
  have hd : (m.divisors.card:ℝ) ≤ 2*(m:ℝ)^(1/2:ℝ) :=
    (show (m.divisors.card:ℝ) ≤ 2*m.sqrt by exact_mod_cast divisors_card_sqrt m).trans (by linarith)
  apply (div_le_div_of_nonneg_right (mul_le_mul hH hd (by positivity) (by positivity)) (by positivity)).trans
  apply le_of_eq
  have he : ((m:ℝ)^(1/4:ℝ)*(m:ℝ)^(1/2:ℝ))*(m:ℝ)^(5/4:ℝ)=(m:ℝ)^2 := by
    rw [← Real.rpow_add hmp,← Real.rpow_add hmp]
    norm_num
  field_simp
  linear_combination 10*he

/-- The aggregate coefficient vector decays as (1 + log q)/q, uniformly in Y. -/
theorem weightedBlock_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y q : ℕ) [NeZero q],
    ‖weightedBlock Y q‖ ≤ C*(1+Real.log q)/q := by
  have hZ : 0 ≤ zetaTwo := (commonWeight_nonneg 1 1).trans (commonWeight_le 1 1)
  have h5 : 0 ≤ zetaFiveFourths := tsum_nonneg fun _ => by positivity
  refine ⟨10*zetaTwo*zetaFiveFourths,by positivity,?_⟩
  intro Y q _
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  apply (weightedBlock_finite_bound Y q).trans
  have hS : ∑ m ∈ Icc 1 (Y/q), ((m:ℝ)^(5/4:ℝ))⁻¹ ≤ zetaFiveFourths :=
    (Real.summable_nat_rpow_inv.mpr (show (1:ℝ)<5/4 by norm_num)).sum_le_tsum _ (by intros; positivity)
  calc
    _ ≤ (zetaTwo/q)*∑ m ∈ Icc 1 (Y/q), 10*(1+Real.log q)*((m:ℝ)^(5/4:ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun m hm => harmonic_divisors (NeZero.pos q)
        (mem_Icc.mp hm).1) (by positivity)
    _ ≤ (zetaTwo/q)*(10*(1+Real.log q)*zetaFiveFourths) := by
      rw [← mul_sum]
      gcongr
    _ = _ := by ring

/-- A coordinate in the finite projection, using a natural numerator. -/
noncomputable def blockCoordinate (Y q h : ℕ) : ℂ :=
  if hq : q=0 then 0 else
    let _ : NeZero q := ⟨hq⟩
    weightedBlock Y q (h : ZMod q)

/-- Squared coefficient mass at frequencies with exact denominator q. -/
noncomputable def primitiveEnergy (Y q : ℕ) : ℝ :=
  ∑ h ∈ (range q).filter (·.Coprime q), ‖blockCoordinate Y q h‖^2

private lemma primitiveEnergy_le (Y q : ℕ) [NeZero q] : primitiveEnergy Y q ≤ ‖weightedBlock Y q‖^2 := by
  unfold primitiveEnergy
  rw [EuclideanSpace.norm_sq_eq]
  apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans_eq
  simp only [blockCoordinate,dif_neg (NeZero.ne q)]
  apply sum_bij (fun (a : ℕ) _ => (a : ZMod q))
  · intros; exact mem_univ _
  · intro a ha b hb H
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),ZMod.val_natCast_of_lt (mem_range.mp hb)]
      using congrArg ZMod.val H
  · intro b _; exact ⟨b.val,mem_range.mpr b.val_lt,ZMod.natCast_zmod_val _⟩
  · intros; rfl

/-- The squared mass on any finite family of exact denominators above Q is
O(Q^(-15/16)). The constant is independent of the original cutoff Y. -/
theorem primitiveEnergy_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y Q : ℕ), 0<Q → ∀ s : Finset ℕ,
    (∀ q ∈ s, Q≤q) → ∑ q ∈ s, primitiveEnergy Y q ≤ C/((Q:ℝ)^(15/16:ℝ)) := by
  obtain ⟨A,hA,hblock⟩ := weightedBlock_bound
  let K := (65*A)^2
  let Z := ∑' n : ℕ, ((n : ℝ)^(33/32:ℝ))⁻¹
  have hK : 0≤K := sq_nonneg _
  have hZ : 0≤Z := tsum_nonneg (by intros; positivity)
  refine ⟨K*Z,mul_nonneg hK hZ,?_⟩
  intro Y Q hQ s hs
  have hQr : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hb (q : ℕ) (ht : Q≤q) : primitiveEnergy Y q ≤
      (K/(Q:ℝ)^(15/16:ℝ))*((q:ℝ)^(33/32:ℝ))⁻¹ := by
    let : NeZero q := ⟨by omega⟩
    have hqr : 0 < (q:ℝ) := by exact_mod_cast (hQ.trans_le ht)
    have hqone : (1:ℝ)≤q := by exact_mod_cast (hQ.trans_le ht)
    have hpow := Real.one_le_rpow hqone (by norm_num : (0:ℝ)≤1/64)
    have hl := Real.log_natCast_le_rpow_div q (by norm_num : (0:ℝ)<1/64)
    have he : (1+Real.log q) ≤ 65*(q:ℝ)^(1/64:ℝ) := by linarith
    have hn := (hblock Y q).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hA) hqr.le)
    apply (primitiveEnergy_le Y q).trans ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ?_)
    have hprod : ((q:ℝ)^(1/64:ℝ))^2*(q:ℝ)^(15/16:ℝ)*(q:ℝ)^(33/32:ℝ) = (q:ℝ)^2 := by
      rw [sq,← Real.rpow_add hqr,← Real.rpow_add hqr,← Real.rpow_add hqr]; norm_num
    have monot := Real.rpow_le_rpow hQr.le (show (Q:ℝ) ≤ q by exact_mod_cast ht)
      (by norm_num : (0:ℝ)≤15/16)
    apply le_trans _ (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hK (by positivity) monot)
      (by positivity))
    apply le_of_eq; dsimp [K]
    field_simp
    first | linear_combination hprod | linear_combination (65*A)^2*hprod | (ring_nf at hprod ⊢; grind)
  calc
    _ ≤ ∑ q ∈ s, (K/(Q:ℝ)^(15/16:ℝ))*((q:ℝ)^(33/32:ℝ))⁻¹ :=
      sum_le_sum fun q hq => hb q (hs q hq)
    _ ≤ (K/(Q:ℝ)^(15/16:ℝ))*Z := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left ((Real.summable_nat_rpow_inv.mpr
        (by norm_num : (1:ℝ)<33/32)).sum_le_tsum _ (by intros; positivity)) (by positivity)
    _ = _ := by ring

end Arxiv.«2501.03234».ThetaReciprocalBlocks
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.weightedBlock_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.primitiveEnergy_tail
