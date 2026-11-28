import ThetaClassTailSize

/-! Explicit lower tail masses of the prime limit law. -/
namespace Arxiv.«2501.03234».ThetaLargeLawTails
open Finset Filter MeasureTheory ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeDensity
open ThetaDiagonalConstant ThetaFactorialSequence ThetaPrimeLaw ThetaProfiniteUnits ThetaClassTailSize
open scoped Topology

theorem sequence_mass (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, 0< C ∧ ∀ᶠ T : ℕ in atTop, ∀ F : G →₁[haar] ℝ, Represents residual F →
      ENNReal.ofReal (1/(C*((modulus T:ℕ):ℝ)^2)) ≤ (haarLaw F : Measure ℝ)
        (Set.Ici (diagonalConstant+(Real.log T)^2/(32*Real.pi^2))) := by
  obtain ⟨C,hC,H⟩ := prime_lower hAP
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with T hT
  intro F hF
  let a := diagonalConstant+(Real.log T)^2/(32*Real.pi^2)
  apply mass_lower_of_count (P:=fun p => a< residual p) isClosed_Ici (empirical_tendsto hAP hF)
  · filter_upwards [hT] with X hX
    simpa only [one_div,div_eq_mul_inv,one_mul,a,ThetaCharacterPrimeMeans.residual,mul_comm _ (X.primeCounting:ℝ)] using hX
  · intro p _ hp; exact hp.le

private theorem modulus_log {T : ℕ} (hT : 0< T) : Real.log (modulus T:ℝ) ≤ (T:ℝ)^3 := by
  have h : T.factorial ≤ T^T := Nat.factorial_le_pow T
  have hl := Real.log_le_log (by exact_mod_cast Nat.factorial_pos T : 0<(T.factorial:ℝ))
     (by exact_mod_cast h : (T.factorial:ℝ) ≤ (T:ℝ)^T)
  rw [Real.log_pow] at hl
  simp only [modulus,Nat.cast_pow,Real.log_pow]
  have hx := Real.log_le_self (Nat.cast_nonneg T)
  nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg T),
    mul_le_mul_of_nonneg_left hx (sq_nonneg (T:ℝ))]

/-- Convert a factorial sequence estimate to a bound at every sufficiently
large real height, with a double exponential lower fraction. -/
theorem height_scale {C : ℝ} (hC : 0 < C) (P : ℕ → Prop) (H : ∀ᶠ T in atTop, P T) :
    ∀ᶠ b : ℝ in atTop, ∃ T : ℕ, P T ∧ b < (Real.log T)^2/(32*Real.pi^2) ∧
      Real.exp (-(Real.exp (32*Real.pi*Real.sqrt b))) ≤ 1/(C*(modulus T:ℝ)^2) := by
  let u (b : ℝ) := Real.exp (8*Real.pi*Real.sqrt b)
  let t (b : ℝ) := ⌈u b⌉₊
  have hu : Tendsto u atTop atTop := Real.tendsto_exp_atTop.comp
    ((tendsto_const_mul_atTop_of_pos (by positivity : 0<8*Real.pi)).mpr Real.tendsto_sqrt_atTop)
  have ht : Tendsto t atTop atTop := tendsto_nat_ceil_atTop.comp hu
  filter_upwards [ht.eventually H,hu.eventually_ge_atTop (max 17 (Real.log C)),eventually_gt_atTop (0:ℝ)] with b h hlarge hb
  let T := t b
  have h1 := (le_max_left 17 (Real.log C)).trans hlarge
  have hlogC := (le_max_right 17 (Real.log C)).trans hlarge
  have hut : u b≤(T:ℝ) := Nat.le_ceil _
  have hT : 0< T := by exact_mod_cast (show (0:ℝ)< T by linarith)
  have ht' : (T:ℝ)≤2*u b := by have hl := Nat.ceil_lt_add_one (show 0≤ u b by dsimp [u]; positivity); dsimp only [T,t]; linarith
  have hheight : b<(Real.log T)^2/(32*Real.pi^2) := by
    have hl := Real.log_le_log (by dsimp [u]; positivity : 0< u b) hut
    simp only [u,Real.log_exp] at hl
    have hh := pow_le_pow_left₀ (by positivity : 0≤8*Real.pi*Real.sqrt b) hl 2
    rw [lt_div_iff₀ (by positivity)]
    nlinarith only [hh,Real.sq_sqrt hb.le,mul_pos hb (sq_pos_of_pos Real.pi_pos)]
  have hm : 0<(modulus T:ℝ) := by exact_mod_cast (pow_pos (Nat.factorial_pos T) T)
  have hex : Real.exp (32*Real.pi*Real.sqrt b) = (u b)^4 := by
    rw [show 32*Real.pi*Real.sqrt b=4*(8*Real.pi*Real.sqrt b) by ring]; exact Real.exp_nat_mul _ 4
  have hcost : Real.log (C*(modulus T:ℝ)^2) ≤ Real.exp (32*Real.pi*Real.sqrt b) := by
    rw [hex,Real.log_mul hC.ne' (by positivity),Real.log_pow]
    have h3 := (modulus_log hT).trans (pow_le_pow_left₀ (Nat.cast_nonneg T) ht' 3)
    have hu3 : u b≤(u b)^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) (by linarith only [h1] : 1≤ u b) 2
      nlinarith only [mul_le_mul_of_nonneg_left hh (by linarith only [h1] : 0≤ u b)]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith only [h3,hlogC,hu3,mul_nonneg (sub_nonneg.mpr h1) (pow_nonneg (by linarith only [h1] : 0≤ u b) 3)]
  have he : Real.exp (-(Real.exp (32*Real.pi*Real.sqrt b))) ≤ 1/(C*(modulus T:ℝ)^2) := by
    rw [one_div,←Real.exp_log (show 0< C*(modulus T:ℝ)^2 by positivity),←Real.exp_neg]
    gcongr
  exact ⟨T,h,hheight,he⟩

/-- A double exponential in the square root of height bounds both tails from below. -/
theorem tails (hAP : ProgressionMangoldt) :
    ∀ᶠ b : ℝ in atTop, ∀ F : G →₁[haar] ℝ, Represents residual F →
      let e := ENNReal.ofReal (Real.exp (-(Real.exp (32*Real.pi*Real.sqrt b))))
      e ≤ (haarLaw F : Measure ℝ) (Set.Ioi (diagonalConstant+b)) ∧
      e ≤ (haarLaw F : Measure ℝ) (Set.Iio (diagonalConstant-b)) := by
  obtain ⟨C,hC,H⟩ := sequence_mass hAP
  filter_upwards [height_scale hC _ H] with b hb
  obtain ⟨T,h,hheight,he⟩ := hb
  intro F hF
  have hbase := (ENNReal.ofReal_le_ofReal he).trans (h F hF)
  constructor
  · exact hbase.trans (measure_mono (fun x hx => by change diagonalConstant+b< x; change diagonalConstant+_≤ x at hx; linarith))
  · let r (x : ℝ) := 2*diagonalConstant-x
    have hr : Measurable r := by dsimp [r]; fun_prop
    apply hbase.trans
    calc _ ≤ (haarLaw F : Measure ℝ) (r ⁻¹' Set.Iio (diagonalConstant-b)) := measure_mono (fun x hx => by
           change 2*diagonalConstant-x< diagonalConstant-b
           change diagonalConstant+_≤ x at hx; linarith)
         _ = (reflectedLaw diagonalConstant (haarLaw F) : Measure ℝ) (Set.Iio (diagonalConstant-b)) := by
           rw [reflectedLaw,ProbabilityMeasure.toMeasure_map,Measure.map_apply hr measurableSet_Iio]
         _ = _ := by rw [law_symmetric hAP hF]
#print axioms height_scale
#print axioms sequence_mass
#print axioms tails
end Arxiv.«2501.03234».ThetaLargeLawTails
