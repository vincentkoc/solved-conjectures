import ThetaExceptionalBudgets
import ThetaFiberSecondMoment
import ThetaUniformExcursionBudget
import ThetaRefinedSignedMean
import ThetaReflectedWindowMeans

/-! Signed excursions in the original prime theta sum with one exceptional character allowed. -/
namespace Arxiv.«2501.03234».ThetaUniformExcursions
open Finset Filter Real ThetaIdentityFiber ThetaConditionalRows ThetaPrimeTailTransfer
open ThetaExceptionalPrimeInput ThetaExceptionalConductor ThetaSiegelWalfiszBand
noncomputable section

def hits (N q r : ℕ) (z v : ℝ) := (band N).filter (fun p => p%q=r ∧ v ≤ z*((S p:ℝ)/p-log p/2))
def height (t : ℝ) := (log t)^2/(64*π^2)

private theorem linear {P : ℕ} [NeZero P] (l r : ℕ) (z : ℝ) (f : ℕ → ℝ) :
    l.totient*unitMean P (fun n => selectClass r l n*(z*f n))=
      z*(l.totient*unitMean P (fun n => selectClass r l n*f n)) := by
  unfold unitMean;simp_rw [show ∀ a b : ℝ,a*(z*b)=z*(a*b) by intros;ring,←mul_sum];ring

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 8192 in
theorem band_hits (H : ThetaExceptionalPrimeInput.Ordinary) : ∃ η : ℝ,0<η ∧ ∃ N₀ : ℕ,∀ᶠ T : ℕ in atTop,
    ∀ N≥N₀,134217728*(T:ℝ) ≤ (log (N:ℝ))^(1/3:ℝ) → ∀ q r : ℕ,0<q → r<q → r.Coprime q → log q ≤ η*log T →
    ∀ z : ℝ,|z|=1 → ((N:ℝ)^64/log N)*exp (-(131072*(T:ℝ))) ≤ ((hits N q r z (height T)).card:ℝ) := by
  classical
  obtain ⟨κ₀,hκ₀,hord⟩ := band_input H
  let κ := min 1 κ₀
  have hκ : 0<κ := lt_min zero_lt_one hκ₀
  have hκ' : κ≤1 := min_le_left ..
  obtain ⟨C,hC,htransfer⟩ := ThetaFiberSecondMoment.transfer
  obtain ⟨D,hD,henergy⟩ := ThetaUniformExcursionBudget.energy
  obtain ⟨N₁,hbud⟩ := ThetaUniformExcursionBudget.budgets (D:=D) hκ
  obtain ⟨η,hη,hsign⟩ := ThetaReflectedWindowMeans.uniform
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hheight : Tendsto (fun T : ℕ => height T) atTop atTop :=
    ((tendsto_pow_atTop (n:=2) (by decide)).comp hlog).atTop_div_const (by positivity : (0:ℝ)<64*π^2)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((((hord.and (hlog.eventually_ge_atTop 1)).and (eventually_ge_atTop 3)).and henergy).and (eventually_ge_atTop N₁))
  refine ⟨η,hη,N₀,?_⟩
  filter_upwards [hsign,hbud,hheight.eventually_ge_atTop (max 1 C),eventually_ge_atTop 2]
    with T hT hbud hα h₂ N hN had q r hq hr hcop hqt z hz
  obtain ⟨⟨⟨⟨⟨f,main,V,hf,hmain,hV,hdata⟩,hL⟩,hN3⟩,hE⟩,hN₁⟩ := hN₀ N hN
  change 1 ≤ log (N:ℝ) at hL
  have hlN : 0<log (N:ℝ) := by linarith
  let m := ThetaCompactModulus.modulus T
  have hm := ThetaCompactModulus.positive T
  let l := lift m f
  let Y := l^768
  obtain ⟨hml,hml',_⟩ := bounds hm hf
  have hl : 0 < l := hm.trans_le hml'
  obtain ⟨hk,hcost,hend⟩ := hbud N hN₁ f hf had
  obtain ⟨hm₁,hqm,b,hb,hbc,hbq,hmodel⟩ := hT q r hq hr hcop hqt z hz
  have hkl : κ*(N:ℝ)^64/log N ≤ main := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)) hlN.le).trans hmain
  have hkV (j : ℕ) : κ*(N:ℝ)^64/(log N*(f:ℝ)^2) ≤ V j := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)) (by positivity)).trans (hV j)
  let mass (j : ℕ) := center f l j main V
  have hlow (j : ℕ) : κ*(N:ℝ)^64/(log N*(l:ℝ)^2) ≤ mass j := lower hκ hlN hm hf hkl hkV
  have F (j : ℕ) := ThetaExceptionalBudgets.fit hκ hκ' hl hL hk (hlow j) hcost
  obtain ⟨_,hlim,hYN,_,_,_,_⟩ := F 0
  have hlY : l≤Y := Nat.le_self_pow (by decide) _
  have hmY := hml'.trans hlY
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero l := ⟨hl.ne'⟩
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  have hmod := hmodel Y hmY N (max_le (hmY.trans hYN) hN3)
  obtain ⟨b',hb',hbc',hres,hbest⟩ := ThetaRefinedSignedMean.best hml (Nat.dvd_factorial hl hlY) hb hbc
    (fun p => z*model Y N p)
  simp only [linear] at hbest
  obtain ⟨hM',_,_,he₁,he₂,he₃,hw⟩ := F b'
  have hcl (d : ℕ) (hd : 0<d) (hd' : d≤Y) := on_fiber (b:=b') hdata hm hf hd hd' hlim
  have h₁ := hcl 1 (by decide) (hl.trans_le hlY);rw [mul_one] at h₁
  let α := height T
  have hhigh : 1≤α := (le_max_left ..).trans hα
  have hCα : C≤α := (le_max_right ..).trans hα
  have hfit : 4*α+C ≤ (8/π^2)*((log T)^2/64) := by
    have h : (8/π^2)*((log T)^2/64)=8*α := by dsimp [α,height];ring
    rw [h];linarith only [hCα,hhigh]
  let L := log (N:ℝ)
  have h := htransfer (band N) (weight N) (by omega : 2≤N) hl hb' hbc' hlY hYN hM' (by unfold error;exact div_nonneg (by positivity) (radius_pos _).le) hz
    (fun _ hp => mem_band.mp hp) (fun _ hp => weights (by omega) hp) h₁
    (fun d hd => hcl d (by have := (mem_Icc.mp hd).1;omega) (mem_Icc.mp hd).2)
    he₁ he₂ he₃ (hmod.trans hbest) (zero_le_one.trans hhigh) hfit
  have hsub : (band N).filter (fun p => p%l=b' ∧ α≤z*((S p:ℝ)/p-log p/2)) ⊆ hits N q r z α := by
    intro p hp;obtain ⟨hh,hb'',he⟩ := mem_filter.mp hp
    have hqm' : q∣l := hqm.trans hml
    refine mem_filter.mpr ⟨hh,?_,he⟩
    rw [←Nat.mod_mod_of_dvd p hqm',hb'',←Nat.mod_mod_of_dvd b' hqm,hres,hbq]
  let K := ((hits N q r z α).card:ℝ)
  let P := (N:ℝ)^64/L
  have hP : 0<P := div_pos (pow_pos (Nat.cast_pos.mpr (by omega : 0<N)) _) hlN
  have hφ := Nat.cast_pos (α:=ℝ).mpr (Nat.totient_pos.mpr hl)
  have hlp := Nat.cast_pos (α:=ℝ).mpr hl
  have hKK : (κ*P/(l:ℝ)^3)^2 ≤ K*(D*P) := by
    have hh : κ*P/(l:ℝ)^3 ≤ (mass b'/l.totient)*α := by
      have heq : κ*P/(l:ℝ)^3=κ*(N:ℝ)^64/(L*(l:ℝ)^3) := by dsimp [P];ring
      rw [heq]
      exact hw.trans (le_mul_of_one_le_right (div_nonneg hM' hφ.le) hhigh)
    exact ((pow_le_pow_left₀ (by positivity) hh 2).trans h).trans (mul_le_mul (Nat.cast_le.mpr (card_le_card hsub))
      hE (sum_nonneg (fun p _ => sq_nonneg _)) (Nat.cast_nonneg _))
  change P*exp (-(131072*(T:ℝ))) ≤ K
  rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
  apply le_trans _ (mul_le_mul_of_nonneg_left hend (show 0≤K by dsimp [K];positivity))
  rw [div_pow,div_le_iff₀ (by positivity)] at hKK
  apply (mul_le_mul_iff_left₀ hP).mp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hκ)).mp
  calc P*P*κ^2 = (κ*P)^2 := by ring
       _ ≤ K*(D*P)*((l:ℝ)^3)^2 := hKK
       _ = K*(D/κ^2*(l:ℝ)^6)*P*κ^2 := by field_simp

#print axioms band_hits
end
end Arxiv.«2501.03234».ThetaUniformExcursions
