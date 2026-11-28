import ThetaFactorialRows
import ThetaOppositeMeans
import ThetaIdentityPrimeMeans

/-! A uniform absolute bound on every limiting congruence predictor. -/
namespace Arxiv.«2501.03234».ThetaUniformClassMeans
open Finset Filter Real ThetaRowCorrelations ThetaIdentityFiber ThetaDivisorLogMean ThetaSmoothRows
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaPrimeTailTransfer
open ThetaPrimeMeanSquare ThetaReciprocalInversion ThetaFactorialRows ThetaIdentityModels
open ThetaNaturalPrimeMeans ThetaProgressionProjection ThetaDiagonalConstant
open scoped Topology
noncomputable section

private theorem model_bound {m r Y : ℕ} (hm : 1 < m) (hr : r < m) (hc : r.Coprime m)
    (hY : m≤ Y) (V : ℕ) :
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    |m.totient*unitMean Y.factorial (fun n => selectClass r m n*model Y V n)| ≤
      (1080*Z*zetaBound)*logMass m := by
  classical
  let P := Y.factorial
  let : NeZero P := ⟨Nat.factorial_ne_zero _⟩
  have hmP : m∣P := Nat.dvd_factorial (by omega) hY
  let K := coneWindow (coneWidth V)
  let a := commonWeight (2*V^52)
  let u (d : ℕ) := a d/d*residueMean r m d P (K d)
  have hZ : 0≤ Z := tsum_nonneg fun _ => by positivity
  have hscale : (m.totient:ℝ)*unitMean P (fun n => selectClass r m n*model Y V n)=∑ d∈Icc 2 Y,u d := by
    change (m.totient:ℝ)*unitMean P (fun n => selectClass r m n*low Y K a n)=_
    rw [mean_low,mul_sum]; apply sum_congr rfl; intro d _
    unfold u residueMean; ring
  have henv (d) (hd : d∈Icc 2 Y) :
      |u d|≤ (1080*Z)*(logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := by
    obtain ⟨hl,hu⟩ := mem_Icc.mp hd
    have H := residue_envelope hm hr hc hl hmP (Nat.dvd_factorial (by omega) hu) (K d)
    obtain ⟨ha,ha'⟩ := commonWeight_bounds (2*V^52) d
    calc _ = a d*(|residueMean r m d P (K d)|/d) := by
             simp only [u,abs_mul,abs_div,abs_of_nonneg (show 0≤ a d from ha),
               abs_of_nonneg (Nat.cast_nonneg d : 0≤ (d:ℝ))]; ring
         _ ≤ Z*(1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) :=
               mul_le_mul ha' H (by positivity) hZ
         _ = _ := by ring
  have hrect := rectangle (m:=m) (Icc 2 Y) m.divisors (Icc 1 Y) (by
    intro d hd
    obtain ⟨hl,hu⟩ := mem_Icc.mp hd
    exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,by omega⟩,
      mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right ..)) (Nat.gcd_pos_of_pos_left _ (by omega)),
        (Nat.div_le_self ..).trans hu⟩⟩)
  have ht := tail (Q:=1) (by decide) (Icc 1 Y) (fun _ h => (mem_Icc.mp h).1)
  norm_num only [Nat.cast_one,Real.one_rpow,div_one] at ht
  have hL : 0≤ logMass m := sum_nonneg fun i _ => logWeight_nonneg i
  have H := (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum henv)
  rw [←mul_sum] at H
  rw [hscale]
  have hrect' := hrect.trans (mul_le_mul_of_nonneg_left ht hL)
  change _ ≤ logMass m*zetaBound at hrect'
  nlinarith only [H,mul_le_mul_of_nonneg_left hrect' (show 0≤ 1080*Z by positivity)]

def constant := (8/Real.pi^2)*(1080*Z*zetaBound)

private theorem lower (hAP : ProgressionMangoldt) {m r : ℕ} [NeZero m] (hm : 1 < m)
    (hr : r < m) (hc : r.Coprime m) : -(constant*logMass m) ≤ predictor m r := by
  have H := ThetaIdentityPrimeMeans.residue_transfer hAP hm hr hc (B:=-((1080*Z*zetaBound)*logMass m)) (by
    filter_upwards [eventually_ge_atTop m] with Y hY
    filter_upwards with V
    exact ⟨Nat.dvd_factorial (by omega) hY,(abs_le.mp (model_bound hm hr hc hY V)).1⟩)
  obtain ⟨L,hL,h⟩ := H
  have he := tendsto_nhds_unique h (original_mean m r hc hr hAP)
  rw [he] at hL
  dsimp only [constant]; linarith

theorem bound (hAP : ProgressionMangoldt) {m r : ℕ} [NeZero m] (hr : r < m)
    (hc : r.Coprime m) : |predictor m r| ≤ constant*logMass m := by
  have hconst : 0≤ constant := by
    have hZ : 0≤ Z := tsum_nonneg fun _ => by positivity
    have hz : 0≤ zetaBound := tsum_nonneg fun _ => by positivity
    dsimp only [constant]; positivity
  have hL : 0≤ logMass m := sum_nonneg fun i _ => logWeight_nonneg i
  by_cases hm : 1< m
  · let v := -ZMod.unitOfCoprime r hc
    let t := (v:ZMod m).val
    have ht : t< m := ZMod.val_lt _
    have htc : t.Coprime m := ZMod.val_coe_unit_coprime _
    have hneg : (t:ZMod m)=-(r:ZMod m) := by simp [t,v]
    have h := lower hAP hm ht htc
    rw [ThetaOppositeMeans.reflection hneg hAP] at h
    exact abs_le.mpr ⟨lower hAP hm hr hc,by linarith⟩
  · have hm' : m=1 := by have := NeZero.pos m; omega
    subst m
    have hv (χ : DirichletCharacter ℂ 1) : ThetaLevelCoefficients.value χ=0 := by
      have he : χ=1 := Subsingleton.elim ..
      simp [ThetaLevelCoefficients.value,he]
    have he : predictor 1 r=0 := by simp [predictor,ThetaFiniteProjection.model,hv]
    rw [he,abs_zero]; exact mul_nonneg hconst hL

#print axioms bound
end
end Arxiv.«2501.03234».ThetaUniformClassMeans
