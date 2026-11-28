import ThetaUniformClassMeans
import ThetaDivisorBudget

/-! Conditional means of finite row models on smooth moduli. -/
namespace Arxiv.«2501.03234».ThetaSmoothConditionalModel
open Finset Filter Real ThetaRowCorrelations ThetaIdentityFiber ThetaDivisorLogMean ThetaSmoothRows
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaPrimeTailTransfer
open ThetaPrimeMeanSquare ThetaReciprocalInversion ThetaFactorialRows ThetaIdentityModels
open ThetaDivisorBudget
noncomputable section

def cond (m r Y V : ℕ) : ℝ :=
  letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  (m.totient:ℝ)*unitMean Y.factorial (fun n => selectClass r m n*model Y V n)

def term (m r Y V d : ℕ) : ℝ :=
  letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  commonWeight (2*V^52) d/d*residueMean r m d Y.factorial (coneWindow (coneWidth V) d)

theorem expand (m r Y V : ℕ) : cond m r Y V = ∑ d∈Icc 2 Y,term m r Y V d := by
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  change (m.totient:ℝ)*unitMean Y.factorial (fun n => selectClass r m n*low Y _ _ n)=_
  rw [mean_low,mul_sum]
  apply sum_congr rfl
  intro d _
  unfold term residueMean
  ring

def envelope := 1080*Z*zetaBound

theorem envelope_nonneg : 0≤envelope := by
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  have hz : 0≤zetaBound := tsum_nonneg fun _ => by positivity
  dsimp [envelope];positivity

theorem restricted {m r Y : ℕ} (hm : 1 < m) (hr : r < m) (hc : r.Coprime m)
    (hmP : m ∣ Y.factorial) (V : ℕ) (D G : Finset ℕ) (hD : D ⊆ Icc 2 Y)
    (hG : ∀ d∈D, m.gcd d∈G) :
    |∑ d∈D,term m r Y V d| ≤ envelope*∑ g∈G,logWeight g := by
  classical
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  have hZ : 0≤ Z := tsum_nonneg fun _ => by positivity
  have henv (d) (hd' : d∈D) :
      |term m r Y V d| ≤ (1080*Z)*(logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := by
    have hd := hD hd'
    obtain ⟨hl,hu⟩ := mem_Icc.mp hd
    have H := residue_envelope hm hr hc hl hmP (Nat.dvd_factorial (by omega) hu) (coneWindow (coneWidth V) d)
    obtain ⟨ha,ha'⟩ := commonWeight_bounds (2*V^52) d
    calc _ = (commonWeight (2*V^52) d)*(|residueMean r m d Y.factorial (coneWindow (coneWidth V) d)|/d) := by
             simp only [term,abs_mul,abs_div,abs_of_nonneg (show 0≤ (commonWeight (2*V^52) d) from ha),
               abs_of_nonneg (Nat.cast_nonneg d : 0≤ (d:ℝ))]; ring
         _ ≤ Z*(1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) :=
               mul_le_mul ha' H (by positivity) hZ
         _ = _ := by ring
  have hrect := rectangle (m:=m) D G (Icc 1 Y) (by
    intro d hd
    obtain ⟨hl,hu⟩ := mem_Icc.mp (hD hd)
    exact ⟨hG d hd, mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right ..))
      (Nat.gcd_pos_of_pos_left _ (by omega)),(Nat.div_le_self ..).trans hu⟩⟩)
  have ht := tail (Q:=1) (by decide) (Icc 1 Y) (fun _ h => (mem_Icc.mp h).1)
  norm_num only [Nat.cast_one,Real.one_rpow,div_one] at ht
  have hL : 0≤ ∑ g∈G,logWeight g := sum_nonneg fun i _ => logWeight_nonneg i
  have H := (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum henv)
  rw [←mul_sum] at H
  have hh := hrect.trans (mul_le_mul_of_nonneg_left ht hL)
  change _ ≤ (∑ g∈G,logWeight g)*zetaBound at hh
  exact H.trans ((mul_le_mul_of_nonneg_left hh (show 0≤1080*Z by positivity)).trans_eq (by dsimp only [envelope];ring))

theorem smooth_bound {m r Y y : ℕ} (hm : 1 < m) (hr : r < m) (hc : r.Coprime m)
    (hmP : m∣Y.factorial) (hy : 0<y) (hlog : 1≤log y) (hs : ∀ q∈m.primeFactors,q≤y) (V : ℕ) :
    |cond m r Y V| ≤ envelope*(238*(log y)^2) := by
  rw [expand]
  have he := restricted hm hr hc hmP V (Icc 2 Y) m.divisors Subset.rfl
    (fun d _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,by omega⟩)
  exact he.trans (mul_le_mul_of_nonneg_left (smooth_bounds (by omega) hy hlog hs).2 envelope_nonneg)

#print axioms restricted
#print axioms smooth_bound
end
end Arxiv.«2501.03234».ThetaSmoothConditionalModel
