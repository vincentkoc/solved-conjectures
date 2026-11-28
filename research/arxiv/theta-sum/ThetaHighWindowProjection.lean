import ThetaSmoothDivisorTails
import ThetaSmoothConditionalModel
import ThetaOrbitProjection

/-! Conditional means of denominator windows above a cutoff, including at nonunits. -/
namespace Arxiv.«2501.03234».ThetaHighWindowProjection
open Finset Real ThetaRowCorrelations ThetaIdentityFiber ThetaDivisorLogMean ThetaSmoothRows
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaPrimeTailTransfer
open ThetaFactorialRows ThetaIdentityModels ThetaDivisorBudget ThetaSmoothConditionalModel
open ThetaSmoothFiltration ThetaExposureLayers ThetaUnitExposure ThetaAllWindowMoments ThetaOrbitProjection
open scoped Classical
noncomputable section

def budget : ℝ := (1080*Z)*zetaBound*(238+858*exp (32*log (3/2)))

theorem conditional {m r Y U Q : ℕ} (hm : 1 < m) (hr : r < m) (hc : r.Coprime m)
    (hdiv : m∣Y.factorial) (hu : 1 ≤ log U) (hsupp : ∀ p∈m.primeFactors,p ≤ U)
    (hQ : 0 < Q) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1/16) (hlog : s*log U ≤ log (3/2))
    (W : Window) (hW : ∀ d,d ≤ Q^2 → W.width d=0) :
    |cond m r Y W| ≤ budget*(log U)^2/(Q:ℝ)^s := by
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let D := (Icc 2 Y).filter (Q^2 < ·)
  let G := m.divisors.filter (Q ≤ ·)
  have hU : 0 < U := by by_contra! h;rw [show U=0 by omega] at hu;norm_num at hu
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  have hz : 0 ≤ zetaBound := tsum_nonneg fun _ => by positivity
  have heq : cond m r Y W=∑ d∈D,term m r Y W d := by
    rw [expand]
    symm;apply sum_subset_zero_on_sdiff (filter_subset ..) _ (by intros;rfl)
    intro d hd;obtain ⟨hi,hout⟩ := mem_sdiff.mp hd
    have hle : d ≤ Q^2 := le_of_not_gt fun h => hout (mem_filter.mpr ⟨hi,h⟩)
    simp [term,residueMean,unitMean,hW d hle,ThetaRowCorrelations.row]
  have H (d : ℕ) (hd : d∈D) :
      |term m r Y W d| ≤ (1080*Z)*(logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := by
    obtain ⟨h₂,hy⟩ := mem_Icc.mp (mem_filter.mp hd).1
    have h := residue_envelope hm hr hc h₂ hdiv (Nat.dvd_factorial (by omega) hy) (W.width d)
    obtain ⟨ha,ha'⟩ := commonWeight_bounds W.weightCutoff d
    calc _ = (commonWeight W.weightCutoff d)*(|residueMean r m d Y.factorial (W.width d)|/d) := by
               simp only [term,abs_mul,abs_div,abs_of_nonneg ha,abs_of_nonneg (Nat.cast_nonneg d : (0:ℝ) ≤ d)];ring
         _ ≤ Z*(1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := mul_le_mul ha' h (by positivity) hZ
         _ = _ := by ring
  have hrect := omitted_by_size (m:=m) (Y:=Y) (show 0 < m by omega) hQ D G (fun d hd =>
    let h := mem_Icc.mp (mem_filter.mp hd).1; ⟨by omega,h.2⟩) (by
      intro d hd hl
      have hd' := (mem_filter.mp hd).2
      have he := Nat.mul_div_cancel' (Nat.gcd_dvd_right m d)
      apply mem_filter.mpr;refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,by omega⟩,?_⟩
      by_contra! hlt
      have := Nat.mul_le_mul hlt.le hl.le;rw [he] at this;nlinarith only [this,hd'])
  have hmain := (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum H)
  rw [←mul_sum] at hmain
  have hbudget := (smooth_bounds (by omega : 0 < m) hU hu hsupp).2
  have htail := ThetaSmoothDivisorTails.tail (by omega : 0 < m) hu hsupp hs hlog hQ
  have hpow := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ Q by exact_mod_cast hQ) hs'
  have small := div_le_div_of_nonneg_left hz (rpow_pos_of_pos (Nat.cast_pos.mpr hQ) s) hpow
  have comb := hrect.trans (add_le_add (mul_le_mul hbudget small (by positivity) (by positivity)) (mul_le_mul_of_nonneg_right htail hz))
  rw [heq]
  exact hmain.trans ((mul_le_mul_of_nonneg_left comb (by positivity : 0 ≤ 1080*Z)).trans_eq (by unfold budget;ring))

theorem ordinary {Y U Q : ℕ} (hY : 2 ≤ Y) (hU : 2 ≤ U) (hl : 1 ≤ log U) (hQ : 0 < Q)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1/16) (hlog : s*log U ≤ log (3/2))
    (W : Window) (hW : ∀ d,d ≤ Q^2 → W.width d=0) (n : ℕ) :
    |smooth Y U (rowModel Y W) n| ≤ budget*(log U)^2/(Q:ℝ)^s := by
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let : NeZero (modulus Y.factorial U) := ⟨(pos (Nat.factorial_pos Y) U).ne'⟩
  obtain ⟨v,hv⟩ := orbit Y U n W
  have h := (hv 1).2
  simp only [Nat.mul_one,unit_value] at h
  rw [h,value,project (divides (Nat.factorial_pos Y) U)]
  apply conditional (two_le hY hU) (Nat.mod_lt _ (pos (Nat.factorial_pos Y) U)) (key_unit (divides (Nat.factorial_pos Y) U) v)
    (divides (Nat.factorial_pos Y) U) hl (prime_bound Y.factorial U) hQ hs hs' hlog
  intro d hd;simp [masked,hW d hd]

#print axioms ordinary
end
end Arxiv.«2501.03234».ThetaHighWindowProjection
