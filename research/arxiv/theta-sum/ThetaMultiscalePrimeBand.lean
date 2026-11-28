import ThetaMultiscaleRows
import ThetaCenteredPrimeBand

/-! Count the exceptional primes on one band for the original signed integer sum. -/
namespace Arxiv.«2501.03234».ThetaMultiscalePrimeBand
open Finset Filter Real ThetaDenominatorBandScales ThetaMultiscaleRows ThetaSmoothConditionalModel
open ThetaDenominatorTails ThetaReciprocalInversion ThetaRowCorrelations ThetaIdentityModels
open scoped Classical
noncomputable section

theorem omitted {h N : ℕ} (hN : 2 ≤ N) (hl : (scale h:ℝ) ≤ log N) : size (scale h) ≤ 2*N^52 := by
  have hr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hP : 0 ≤ (scale h:ℝ) := by positivity
  have he : log (size (scale h):ℝ) ≤ log ((N:ℝ)^52) := by
    rw [log_size,log_pow];norm_num
    nlinarith only [hl,hP,mul_le_mul_of_nonneg_left (show log 2 ≤ 1 by linarith [log_two_lt_d9]) hP]
  have hh := (Real.log_le_log_iff (by dsimp [size];positivity) (pow_pos hr _)).mp he
  have hn : size (scale h) ≤ N^52 := by exact_mod_cast hh
  omega

theorem raw : ∃ C B : ℝ,0 < C ∧ 0 ≤ B ∧ ∀ᶠ h : ℕ in atTop,∀ N : ℕ,2 ≤ N → (scale h:ℝ) ≤ log N →
    ∀ V : Finset ℕ,(∀ p∈V,p.Prime ∧ N^56 ≤ p ∧ p ≤ N^64 ∧
      C+(8/π^2)*(level h+1) ≤ |(S p:ℝ)/p-log p/2|) →
    (V.card:ℝ) ≤ B*(N:ℝ)^64/(size (scale h):ℝ)^(1/64:ℝ)+((h:ℝ)+2)*error h (N^64+1) := by
  obtain ⟨C,hC,ctrl⟩ := ThetaPrimeMeanSquare.scale_window_control
  obtain ⟨B,hB,hv⟩ := cut_variance
  refine ⟨C,B,hC,hB,?_⟩
  filter_upwards [ThetaMultiscaleRows.count,ThetaMultiscaleRows.outside] with h hcount hout N hN hlog V hV
  obtain ⟨L,hL,hctrl⟩ := ctrl N hN
  let T := size (scale h)
  let Y := 2*N^52
  let X := N^64+1
  let W : Window := ⟨L,Y⟩
  let E := ThetaMultiscaleRows.exceptions h X W
  let F := windowExtension (above T L) Y
  have hT : 0 < T := by dsimp [T,size];positivity
  have hF := hv (T:=T) (by omega) (above T L) (fun d hd => by simp [above,hd]) N (by omega)
  have hs : V⊆range X := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hV p hp).2.2.1)
  have H (p : ℕ) (hp : p∈V\E) : 1 ≤ ‖F p‖^2 := by
    obtain ⟨hh,hne⟩ := mem_sdiff.mp hp
    obtain ⟨hpr,hlo,hhi,he⟩ := hV p hh
    have hY := ThetaPrimeDensity.cutoff_inside hN hlo
    have hcop (d : ℕ) (hd : d∈Icc 1 Y) : p.Coprime d :=
      hpr.coprime_iff_not_dvd.mpr (fun hd' => (lt_of_le_of_lt (mem_Icc.mp hd).2 hY).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 hd'))
    have hsplit : windowExtension L Y p=(rowModel T W p:ℂ)+F p := sub_eq_iff_eq_add.mp (window_split (omitted hN hlog) L hL hcop)
    have hlow := hout X p W (mem_range.mp (hs hh)) hne
    change |rowModel T W p| ≤ level h at hlow
    have hc : 0 < 8/π^2 := by positivity
    have HH := hctrl p hpr hlo hhi
    change _ ≤ C+(8/π^2)*‖windowExtension L Y p‖ at HH
    rw [hsplit] at HH
    have HN := norm_add_le ((rowModel T W p:ℝ):ℂ) (F p)
    rw [Complex.norm_real,Real.norm_eq_abs] at HN
    apply one_le_pow₀
    by_contra! hl
    have hy := calc ‖(rowModel T W p:ℂ)+F p‖ ≤ _ := HN
                    _ < level h+1 := add_lt_add_of_le_of_lt hlow hl
    linarith only [HH,he,mul_lt_mul_of_pos_left hy hc]
  have bound : ((V\E).card:ℝ) ≤ B*(N:ℝ)^64/(T:ℝ)^(1/64:ℝ) := calc
    _ = ∑ _p∈V\E,(1:ℝ) := by simp
    _ ≤ ∑ p∈V\E,‖F p‖^2 := sum_le_sum H
    _ ≤ ∑ p∈range X,‖F p‖^2 := sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans hs) (fun p _ _ => sq_nonneg _)
    _ ≤ _ := hF
  have hc : (V.card:ℝ) ≤ ((V\E).card:ℝ)+(E.card:ℝ) := by exact_mod_cast card_le_card_sdiff_add_card (s:=V) (t:=E)
  exact hc.trans (add_le_add bound (hcount X W))

#print axioms raw
end
end Arxiv.«2501.03234».ThetaMultiscalePrimeBand
