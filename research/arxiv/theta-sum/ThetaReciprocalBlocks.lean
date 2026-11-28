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

/-- Euclidean norm of the projection of one primitive numerator. -/
theorem numeratorVector_bound (q m w : ℕ) [NeZero q] :
    ‖numeratorVector q m w‖ ≤ m.divisors.card / (m : ℝ) := by
  unfold numeratorVector
  split_ifs with H
  · let : NeZero (q*m) := ⟨(Nat.mul_pos (NeZero.pos q) (by omega)).ne'⟩
    have he := reciprocalCoeff_energy H.1 H.2.1 (ZMod.unitOfCoprime w H.2.2.2)
    rw [EuclideanSpace.norm_eq,Real.sqrt_le_iff]
    exact ⟨by positivity,he⟩
  · rw [norm_zero]; positivity

/-- Projection of the positive numerators up to n at denominator q*m. -/
noncomputable def numeratorWindow (q m n : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  ∑ k ∈ range n, (((k : ℝ)+1)⁻¹) • numeratorVector q m (k+1)

theorem numeratorWindow_bound (q m n : ℕ) [NeZero q] :
    ‖numeratorWindow q m n‖ ≤ (harmonic n:ℝ)*(m.divisors.card/(m:ℝ)) := by
  apply (norm_sum_le ..).trans
  have hr : (harmonic n:ℝ) = ∑ k ∈ range n, ((k:ℝ)+1)⁻¹ := by simp [harmonic]
  rw [hr,sum_mul]
  apply sum_le_sum; intro k _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (numeratorVector_bound ..) (by positivity)

/-- All primitive numerators below the original denominator, projected to q. -/
noncomputable def numeratorRow (q m : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  numeratorWindow q m (q*m-1)

/-- Harmonic numbers are increasing after casting to the reals. -/
theorem harmonic_mono_real {n m : ℕ} (h : n ≤ m) : (harmonic n:ℝ)≤harmonic m := by
  simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply sum_le_sum_of_subset_of_nonneg (range_mono h) (by intros; positivity)

/-- Grouping the harmonic sum into K blocks bounds it by K copies of its first block. -/
theorem harmonic_product (K d : ℕ) : (harmonic (K*d):ℝ) ≤ K*(harmonic d:ℝ) := by
  induction K with
  | zero => simp [harmonic]
  | succ K ih =>
    have h (n : ℕ) : (harmonic n:ℝ) = ∑ i ∈ range n, ((i:ℝ)+1)⁻¹ := by simp [harmonic]
    have he : (harmonic (K*d+d):ℝ) ≤ harmonic (K*d)+(harmonic d:ℝ) := by
      rw [h,h,h,sum_range_add]; apply add_le_add le_rfl
      apply sum_le_sum; intro i _; push_cast; gcongr; linarith [mul_nonneg (Nat.cast_nonneg K : (0:ℝ)≤K) (Nat.cast_nonneg d)]
    rw [Nat.succ_mul,Nat.cast_succ,add_mul,one_mul]
    exact he.trans (add_le_add ih le_rfl)

private lemma numeratorRow_bound (q m : ℕ) [NeZero q] :
    ‖numeratorRow q m‖ ≤ (harmonic (q*m):ℝ)*(m.divisors.card/(m:ℝ)) :=
  (numeratorWindow_bound q m _).trans (mul_le_mul_of_nonneg_right
    (harmonic_mono_real (Nat.sub_le (q*m) 1)) (by positivity))

/-- The entire weighted block at projected denominator q. Its primitive coordinates
are exactly the frequencies with reduced denominator q in the cutoff expansion. -/
noncomputable def weightedBlock (Y q : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  ∑ m ∈ Icc 1 (Y/q), (commonWeight Y (q*m) / ((q:ℝ)*m)) • numeratorRow q m

private lemma aggregate_finite_bound (Y q : ℕ) [NeZero q] (B : ℝ)
    (R : ℕ → EuclideanSpace ℂ (ZMod q))
    (hr : ∀ m ∈ Icc 1 (Y/q), ‖R m‖ ≤ B*((harmonic (q*m):ℝ)*(m.divisors.card/(m:ℝ)))) :
    ‖∑ m ∈ Icc 1 (Y/q), (commonWeight Y (q*m)/((q:ℝ)*m)) • R m‖ ≤ (B*(zetaTwo / q)) *
      ∑ m ∈ Icc 1 (Y/q), (harmonic (q*m) : ℝ) * m.divisors.card / (m:ℝ)^2 := by
  apply (norm_sum_le ..).trans
  rw [mul_sum]
  apply sum_le_sum; intro m hm
  have hm' : 0<(m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
  have hq' : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (commonWeight_nonneg ..) (by positivity))]
  apply (mul_le_mul (div_le_div_of_nonneg_right (commonWeight_le ..) (by positivity))
    (hr m hm) (norm_nonneg _) (div_nonneg ((commonWeight_nonneg ..).trans
      (commonWeight_le Y (q*m))) (by positivity))).trans
  apply le_of_eq; ring

/-- Pair divisors across the square root to bound their number. -/
theorem divisors_card_sqrt (m : ℕ) : m.divisors.card ≤ 2*m.sqrt := by
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

/-- Any projected numerator rows with the harmonic divisor bound give aggregate
decay of order (1 + log q)/q, uniformly in the denominator cutoff. -/
theorem aggregate_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y q : ℕ) [NeZero q],
    ∀ (B : ℝ), 0≤B → ∀ R : ℕ → EuclideanSpace ℂ (ZMod q),
      (∀ m ∈ Icc 1 (Y/q), ‖R m‖ ≤ B*((harmonic (q*m):ℝ)*(m.divisors.card/(m:ℝ)))) →
      ‖∑ m ∈ Icc 1 (Y/q), (commonWeight Y (q*m)/((q:ℝ)*m)) • R m‖ ≤ (B*C)*(1+Real.log q)/q := by
  have hZ : 0 ≤ zetaTwo := (commonWeight_nonneg 1 1).trans (commonWeight_le 1 1)
  have h5 : 0 ≤ zetaFiveFourths := tsum_nonneg fun _ => by positivity
  refine ⟨10*zetaTwo*zetaFiveFourths,by positivity,?_⟩
  intro Y q _ B hB R hr
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  apply (aggregate_finite_bound Y q B R hr).trans
  have hS : ∑ m ∈ Icc 1 (Y/q), ((m:ℝ)^(5/4:ℝ))⁻¹ ≤ zetaFiveFourths :=
    (Real.summable_nat_rpow_inv.mpr (show (1:ℝ)<5/4 by norm_num)).sum_le_tsum _ (by intros; positivity)
  calc
    _ ≤ (B*(zetaTwo/q))*∑ m ∈ Icc 1 (Y/q), 10*(1+Real.log q)*((m:ℝ)^(5/4:ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun m hm => harmonic_divisors (NeZero.pos q)
        (mem_Icc.mp hm).1) (by positivity)
    _ ≤ (B*(zetaTwo/q))*(10*(1+Real.log q)*zetaFiveFourths) := by
      rw [← mul_sum]
      gcongr
    _ = _ := by ring

/-- The aggregate coefficient vector decays as (1 + log q)/q, uniformly in Y. -/
theorem weightedBlock_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y q : ℕ) [NeZero q],
    ‖weightedBlock Y q‖ ≤ C*(1+Real.log q)/q := by
  obtain ⟨C,hC,h⟩ := aggregate_bound
  refine ⟨C,hC,?_⟩; intro Y q _
  simpa only [weightedBlock,one_mul] using h Y q 1 zero_le_one (fun m => numeratorRow q m)
    (fun m _ => (numeratorRow_bound q m).trans_eq (one_mul _).symm)

/-- Aggregate coefficient vector when denominator d admits L(d) positive numerators. -/
noncomputable def windowBlock (L : ℕ → ℕ) (Y q : ℕ) [NeZero q] : EuclideanSpace ℂ (ZMod q) :=
  ∑ m ∈ Icc 1 (Y/q), (commonWeight Y (q*m)/((q:ℝ)*m)) • numeratorWindow q m (L (q*m))

/-- A fixed-width window retains the logarithmic-over-denominator decay. -/
theorem windowBlock_bound {L : ℕ → ℕ} {K : ℕ} (hL : ∀ d, L d≤K*d) :
    ∃ C : ℝ, 0≤C ∧ ∀ (Y q : ℕ) [NeZero q], ‖windowBlock L Y q‖ ≤ C*(1+Real.log q)/q := by
  obtain ⟨C,hC,h⟩ := aggregate_bound
  refine ⟨K*C,by positivity,?_⟩
  intro Y q _
  apply h Y q K (Nat.cast_nonneg K)
  intro m _
  apply (numeratorWindow_bound q m _).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((harmonic_mono_real (hL _)).trans (harmonic_product K _)) (by positivity)

/-- Coordinates of an aggregate window on the additive frequencies. -/
noncomputable def windowCoordinate (L : ℕ → ℕ) (Y q h : ℕ) : ℂ :=
  if hq : q=0 then 0 else
    let _ : NeZero q := ⟨hq⟩
    windowBlock L Y q (h:ZMod q)

/-- A coordinate in the finite projection, using a natural numerator. -/
noncomputable def blockCoordinate (Y q h : ℕ) : ℂ :=
  if hq : q=0 then 0 else
    let _ : NeZero q := ⟨hq⟩
    weightedBlock Y q (h : ZMod q)

/-- Squared coefficient mass at frequencies with exact denominator q. -/
noncomputable def primitiveEnergy (Y q : ℕ) : ℝ :=
  ∑ h ∈ (range q).filter (·.Coprime q), ‖blockCoordinate Y q h‖^2

/-- Restricting a coefficient vector to primitive frequencies decreases its squared mass. -/
theorem primitive_mass_le (q : ℕ) [NeZero q] (b : EuclideanSpace ℂ (ZMod q)) :
    ∑ h ∈ (range q).filter (·.Coprime q), ‖b (h:ZMod q)‖^2 ≤ ‖b‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans_eq
  apply sum_bij (fun (a : ℕ) _ => (a : ZMod q))
  · intros; exact mem_univ _
  · intro a ha b hb H
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),ZMod.val_natCast_of_lt (mem_range.mp hb)]
      using congrArg ZMod.val H
  · intro b _; exact ⟨b.val,mem_range.mpr b.val_lt,ZMod.natCast_zmod_val _⟩
  · intros; rfl

/-- A uniform logarithmic-over-denominator bound on the square root of each
frequency mass implies power decay of the tail. -/
theorem energy_tail_of_bound (E : ℕ → ℕ → ℝ) (A : ℝ) (hA : 0≤A)
    (hblock : ∀ Y q : ℕ, 0<q → E Y q ≤ (A*(1+Real.log q)/q)^2) :
    ∃ C : ℝ, 0≤C ∧ ∀ Y Q : ℕ, 0<Q → ∀ s : Finset ℕ,
    (∀ q ∈ s, Q≤q) → ∑ q ∈ s, E Y q ≤ C/(Q:ℝ)^(15/16:ℝ) := by
  let K := (65*A)^2
  let Z := ∑' n : ℕ, ((n : ℝ)^(33/32:ℝ))⁻¹
  have hK : 0≤K := sq_nonneg _
  have hZ : 0≤Z := tsum_nonneg (by intros; positivity)
  refine ⟨K*Z,mul_nonneg hK hZ,?_⟩
  intro Y Q hQ s hs
  have hQr : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hb (q : ℕ) (ht : Q≤q) : E Y q ≤
      (K/(Q:ℝ)^(15/16:ℝ))*((q:ℝ)^(33/32:ℝ))⁻¹ := by
    have hqr : 0 < (q:ℝ) := by exact_mod_cast (hQ.trans_le ht)
    have hqone : (1:ℝ)≤q := by exact_mod_cast (hQ.trans_le ht)
    have hpow := Real.one_le_rpow hqone (by norm_num : (0:ℝ)≤1/64)
    have hl := Real.log_natCast_le_rpow_div q (by norm_num : (0:ℝ)<1/64)
    have he : (1+Real.log q) ≤ 65*(q:ℝ)^(1/64:ℝ) := by linarith
    have hn := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hA) hqr.le
    have h₀ : 0≤A*(1+Real.log q)/(q:ℝ) := by have := Real.log_nonneg hqone; positivity
    apply (hblock Y q (hQ.trans_le ht)).trans ((pow_le_pow_left₀ h₀ hn 2).trans ?_)
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

/-- The squared mass on any finite family of exact denominators above Q is
O(Q^(-15/16)). The constant is independent of the original cutoff Y. -/
theorem primitiveEnergy_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y Q : ℕ), 0<Q → ∀ s : Finset ℕ,
    (∀ q ∈ s, Q≤q) → ∑ q ∈ s, primitiveEnergy Y q ≤ C/((Q:ℝ)^(15/16:ℝ)) := by
  obtain ⟨A,hA,h⟩ := weightedBlock_bound
  apply energy_tail_of_bound primitiveEnergy A hA
  intro Y q hq
  let : NeZero q := ⟨hq.ne'⟩
  apply le_trans _ (pow_le_pow_left₀ (norm_nonneg _) (h Y q) 2)
  simpa only [primitiveEnergy,blockCoordinate,dif_neg hq.ne'] using primitive_mass_le q (weightedBlock Y q)

/-- Primitive frequencies of any fixed-width numerator window have a uniformly
power-decaying squared tail. -/
theorem windowEnergy_tail {L : ℕ → ℕ} {K : ℕ} (hL : ∀ d, L d≤K*d) :
    ∃ C : ℝ, 0≤C ∧ ∀ Y Q : ℕ, 0<Q → ∀ s : Finset ℕ, (∀ q ∈ s, Q≤q) →
    ∑ q ∈ s, ∑ h ∈ (range q).filter (·.Coprime q), ‖windowCoordinate L Y q h‖^2 ≤
      C/(Q:ℝ)^(15/16:ℝ) := by
  obtain ⟨A,hA,ha⟩ := windowBlock_bound hL
  apply energy_tail_of_bound _ A hA
  intro Y q hq
  let : NeZero q := ⟨hq.ne'⟩
  apply le_trans _ (pow_le_pow_left₀ (norm_nonneg _) (ha Y q) 2)
  simpa only [windowCoordinate,dif_neg hq.ne'] using primitive_mass_le q (windowBlock L Y q)

end Arxiv.«2501.03234».ThetaReciprocalBlocks
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.weightedBlock_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.primitiveEnergy_tail
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.divisors_card_sqrt
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.numeratorVector_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.numeratorWindow_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.aggregate_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.windowBlock_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.primitive_mass_le
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.energy_tail_of_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.windowEnergy_tail
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.harmonic_mono_real
#print axioms Arxiv.«2501.03234».ThetaReciprocalBlocks.harmonic_product
