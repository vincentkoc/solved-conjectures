import ThetaCenteredWindow
import ThetaWindowFiniteMoments
import ThetaIntervalPowerEndpoint

/-! Finite-interval moments of the centered row sum. Centering each summand
preserves its individual denominator period. -/
namespace Arxiv.«2501.03234».ThetaCenteredMoment
open Real Finset Filter ThetaCenteredWindow ThetaSmoothConditionalModel ThetaOrbitProjection
open ThetaReciprocalBlocks ThetaIdentityModels ThetaRowCorrelations ThetaPeriodMeans
open ThetaAllWindowMoments ThetaWindowFiniteMoments ThetaTiltBudget
noncomputable section

theorem smooth_sum (Y T n : ℕ) (f : ℕ → ℕ → ℝ) :
    smooth Y T (fun a => ∑ d∈Icc 2 Y,f d a) n=∑ d∈Icc 2 Y,smooth Y T (f d) n := by
  unfold smooth ThetaFiniteExposure.avg
  rw [sum_comm,sum_div]

theorem smooth_bound {B : ℝ} {f : ℕ → ℝ} (hf : ∀ n,|f n|≤B) (Y T n : ℕ) :
    |smooth Y T f n|≤B := by
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let k := ThetaUnitExposure.key (P:=Y.factorial) (ThetaSmoothFiltration.modulus Y.factorial T)
  let A := ThetaFiniteExposure.fiber k (k 1)
  have hc : 0<(A.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr (ThetaFiniteExposure.fiber_nonempty k 1))
  change |(∑ u∈A,f (n*(u:ZMod Y.factorial).val))/(A.card:ℝ)|≤B
  rw [abs_div,abs_of_pos hc,div_le_iff₀ hc]
  calc _ ≤ ∑ u∈A,|f (n*(u:ZMod Y.factorial).val)| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _u∈A,B := sum_le_sum fun u _ => hf _
       _ = _ := by simp [mul_comm]

theorem translated : ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (W : Window) (M X k : ℕ),
    (∑ n∈range X,(center Y T W (M+n))^k) ≤
      (X:ℝ)*(2*exp total)*((k:ℝ)/tilt T)^k+2*(12*Z*(Y:ℝ)^2)^k := by
  filter_upwards [absolute,eventually_ge_atTop 1] with T H hT
  intro Y W M X k
  have ha := tilt_pos hT
  have hz : 0≤Z := tsum_nonneg (fun _ => by positivity)
  let f (d n : ℕ) := (commonWeight W.weightCutoff d/d)*row d (W.width d) n
  have hf (d : ℕ) : OnMod d (f d) := fun n =>
    congrArg (fun z => commonWeight W.weightCutoff d/d*z) (row_onMod d (W.width d) n)
  have hb (d : ℕ) (hd : d∈Icc 2 Y) (n : ℕ) : |f d n|≤6*Z := weighted_bound (mem_Icc.mp hd).1 W n
  let g (d n : ℕ) := f d n-smooth Y T (f d) n
  have hg (d : ℕ) : OnMod d (g d) := fun n => by dsimp only [g];rw [hf d n,smooth_periodic (hf d) Y T n]
  have he (n : ℕ) : (∑ d∈Icc 2 Y,g d n)=center Y T W n := by
    dsimp only [center,g,rowModel,low]
    rw [sum_sub_distrib,←smooth_sum]
    rfl
  have h := ThetaIntervalPowerEndpoint.translated_power (Y:=Y) g M X k
    (show 0≤12*Z by positivity) (fun d _ => hg d) (fun d hd n =>
      (abs_sub _ _).trans (by linarith only [hb d hd n,smooth_bound (hb d hd) Y T n]))
  simp_rw [he] at h
  have hm : mean Y.factorial (fun n => (center Y T W n)^k) ≤ ((k:ℝ)/tilt T)^k*(2*exp total) := by
    have h₁ := sum_le_sum (s:=range Y.factorial) (fun n _ => pointwise_power ha k (center Y T W n))
    rw [← mul_sum] at h₁
    apply (div_le_div_of_nonneg_right h₁ (Nat.cast_nonneg Y.factorial (α:=ℝ))).trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (H Y W) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) ha.le) _)
  exact h.trans (by linarith only [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg X)])

theorem finite : ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (W : Window) (X k : ℕ),
    (∑ n∈range X,(center Y T W n)^k) ≤
      (X:ℝ)*(2*exp total)*((k:ℝ)/tilt T)^k+2*(12*Z*(Y:ℝ)^2)^k := by
  filter_upwards [translated] with T h
  intro Y W X k
  simpa only [Nat.zero_add] using h Y W 0 X k

#print axioms translated
#print axioms finite
end
end Arxiv.«2501.03234».ThetaCenteredMoment
