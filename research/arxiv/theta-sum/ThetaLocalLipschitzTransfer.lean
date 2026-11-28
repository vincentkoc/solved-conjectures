import ThetaLocalPeriodicPrediction

/-! Bounded periodic weights and Lipschitz tests of the residual pass from
dyadic prime windows to all eligible short intervals. -/
namespace Arxiv.«2501.03234».ThetaLocalLipschitzTransfer
open Real Filter Finset ThetaLocalPrimeCounts ThetaLocalDyadicReference ThetaLocalModelComparison
open ThetaLocalPeriodicPrediction ThetaCalibratedCone ThetaCharacterPrimeMeans ThetaPrimeLaw
open ThetaRowProgressionDiscrepancy ThetaConditionalRows ThetaPeriodMeans
open scoped NNReal
noncomputable section

theorem periodic_mean {θ : ℝ} (h : Ordinary θ) {q : ℕ} [NeZero q] {g : ℕ → ℝ} (hg : OnMod q g)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    |avg X H g-unitMean q g|≤ε := by
  let A := ∑ b∈range q,|g b|
  have ha : 0≤A := sum_nonneg (fun _ _ => abs_nonneg _)
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [classes h 1 2,ht.eventually_ge_atTop (q:ℝ),ht.eventually_ge_atTop (2*A/ε),
    ThetaLocalMomentBudgets.count h,eventually_ge_atTop (2:ℕ)] with X hcl hq hL hcnt hx
  intro H hHX hlen
  have hLp : 0<log (X:ℝ) := log_pos (by exact_mod_cast hx)
  change (q:ℝ)≤log (X:ℝ) at hq
  apply normalized (hcnt H hHX hlen).1
  apply (periodic (hcl H hHX hlen q (NeZero.pos q) (by rw [pow_one];exact hq)) hg).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (mass_lower hx hHX) hε.le)
  change A*((H:ℝ)/(log X)^2)≤ε*((H:ℝ)/(2*log X))
  rw [←mul_div_assoc,←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  have hc := (div_le_iff₀ hε).mp hL
  change 2*A≤log (X:ℝ)*ε at hc
  nlinarith only [mul_le_mul_of_nonneg_right hc (show 0≤H*log (X:ℝ) by positivity)]

private theorem weighted_gap {X H : ℕ} {f b w : ℕ → ℝ} {K : ℝ≥0} {φ : ℝ → ℝ}
    (hφ : LipschitzWith K φ) (hw : ∀ p,|w p|≤1) {t : ℝ} (ht : 0<t) (hm : 0< mass X H)
    (hsize : ((sample X H).card:ℝ)≤2*mass X H)
    (hclose : avg X H (fun p => (f p-b p)^2)≤t^2) :
    |avg X H (fun p => w p*φ (f p))-avg X H (fun p => w p*φ (b p))|≤2*K*t := by
  have hE := (div_le_iff₀ hm).mp hclose
  have hsum := ThetaLocalPowerStability.half_error f b 1 ht hsize (by simpa only [mul_one,sq_abs] using hE)
  simp only [pow_one] at hsum
  unfold avg
  rw [←sub_div,abs_div,abs_of_pos hm,div_le_iff₀ hm,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have hs (p : ℕ) (_ : p∈sample X H) : |w p*φ (f p)-w p*φ (b p)|≤K*|f p-b p| := by
    rw [←mul_sub,abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hw p)).trans (hφ.dist_le_mul ..)
  apply (sum_le_sum hs).trans
  rw [←mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (show 0≤(K:ℝ) from K.2)).trans_eq (by ring)

theorem compare {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ) {q : ℕ} (hq : 0<q)
    {w : ℕ → ℝ} (hw : OnMod q w) (hB : ∀ p, |w p|≤1) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    let f (p : ℕ) := w p*φ (residual p)
    |avg X H f-avg X X f|<ε := by
  let t := ε/(16*((K:ℝ)+1))
  have ht : 0<t := by dsimp [t];positivity
  have heq : t*(16*((K:ℝ)+1))=ε := by dsimp [t];field_simp
  obtain ⟨T,V,hmodel⟩ := original he h48 hk hθ hθ₁ h (sq_pos_of_pos ht)
  let b := residualModel T V
  let g (p : ℕ) := w p*φ (b p)
  let P := q*T.factorial
  let : NeZero P := ⟨(Nat.mul_pos hq (Nat.factorial_pos _)).ne'⟩
  have hper : OnMod P g := fun n => congrArg₂ (·*·) (onMod_lift (dvd_mul_right q _) hw n)
    (congrArg φ (onMod_lift (dvd_mul_left _ _) (residualModel_periodic T V) n))
  filter_upwards [hmodel,periodic_mean h hper (show 0<ε/8 by positivity),ThetaLocalMomentBudgets.count h,
    eventually_ge_atTop (1:ℕ)] with X hmod hper' hcnt hx
  let f (p : ℕ) := w p*φ (residual p)
  have half (H : ℕ) (hHX : H≤X) (hlen : (X:ℝ)^θ≤H) :
      |avg X H f-unitMean P g|≤2*K*t+ε/8 := by
    obtain ⟨hm,hs⟩ := hcnt H hHX hlen
    have hh : |avg X H f-avg X H g|≤2*K*t := weighted_gap hφ hB ht hm hs (hmod H hHX hlen)
    exact (abs_sub_le _ (avg X H g) _).trans (add_le_add hh (hper' H hHX hlen))
  intro H hHX hlen _
  have h₁ := half H hHX hlen
  have h₂ := half X le_rfl (full_length hx hθ₁)
  rw [abs_sub_comm (avg X X f)] at h₂
  change |avg X H f-avg X X f|<ε
  nlinarith only [abs_sub_le (avg X H f) (unitMean P g) (avg X X f),h₁,h₂,heq,ht,hε]

#print axioms compare
end
end Arxiv.«2501.03234».ThetaLocalLipschitzTransfer
