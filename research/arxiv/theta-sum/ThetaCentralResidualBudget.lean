import ThetaTernaryTransfer
import ThetaLocalMomentComparison

/-! A bounded second moment on the prime window centered at the target divided by three. -/
namespace Arxiv.«2501.03234».ThetaCentralResidualBudget
open Real Filter Finset MeasureTheory ThetaTernaryErrorBudget ThetaTernaryWindows ThetaCalibratedCone
open ThetaCharacterPrimeMeans ThetaLocalPrimeCounts ThetaLocalDyadicReference
noncomputable section

theorem mass_upper {X H : ℕ} (hX : 2≤X) : mass X H≤(H:ℝ)/log X := by
  have hx : (2:ℝ)≤X := by exact_mod_cast hX
  have hx₀ : 0<(X:ℝ) := by linarith
  have hl : 0<log (X:ℝ) := log_pos (by linarith)
  have ha : (X:ℝ)≤X+H := by linarith [Nat.cast_nonneg (α:=ℝ) H]
  have h₀ : IntervalIntegrable (fun t : ℝ => (log t)⁻¹) volume (X:ℝ) (X+H) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    have hp : 1<t := by linarith only [hx,ht.1]
    exact ((continuousAt_log (by linarith : t≠0)).inv₀ (log_pos hp).ne').continuousWithinAt
  have h := intervalIntegral.integral_mono_on ha h₀ (g:=fun _ : ℝ => (log X)⁻¹) (by simp)
    (fun t ht => inv_anti₀ hl (log_le_log hx₀ ht.1))
  simpa [mass,intervalIntegral.integral_const,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

theorem short {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e) {β : ℝ}
    (hβ : (e:ℝ)/64<β) (hβ' : β≤1) (ord : Ordinary β) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,H≤X → (X:ℝ)^β≤H →
      (∑ p∈sample X H,(residual p)^2)*log X ≤ C*H := by
  obtain ⟨D,hD,hd⟩ := dyadic_moments 2
  have hcomp := ThetaLocalMomentComparison.original he ht hk hβ hβ' ord (q:=1) (by decide)
    (fun _ => (1:ℝ)) (fun _ => (0:ℝ)) (fun _ => rfl) (fun _ => rfl) (by intro;norm_num)
    (D:=0) (by intro;norm_num) 2 (show (0:ℝ)<1 by norm_num)
  refine ⟨D+1,by positivity,?_⟩
  filter_upwards [hd,hcomp,eventually_ge_atTop (2:ℕ)] with X hd hc hx H hh hlen
  have hxp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have hpos : 0<(H:ℝ) := (rpow_pos_of_pos hxp β).trans_le hlen
  have hM : 0 < mass X H := (div_pos hpos (by positivity)).trans_le (mass_lower hx hh)
  have hM' : 0 < mass X X := (div_pos hxp (by positivity)).trans_le (mass_lower hx (le_refl X))
  have hdx : avg X X (fun p => (residual p)^2)≤D := by
    apply (div_le_iff₀ hM').mpr
    simpa only [sq_abs] using hd
  have hs := (abs_le.mp (hc H hh hlen)).2
  simp only [zero_add,one_mul] at hs
  have hsum : (∑ p∈sample X H,(residual p)^2)≤(D+1)*mass X H :=
    (div_le_iff₀ hM).mp (show avg X H (fun p => (residual p)^2)≤D+1 by linarith only [hs,hdx])
  have h := hsum.trans (mul_le_mul_of_nonneg_left (mass_upper hx) (by positivity))
  rw [←mul_div_assoc] at h
  exact (le_div_iff₀ hl).mp h

def Second (θ : ℝ) := ∃ K : ℝ, 0<K ∧ ∀ᶠ n : ℕ in atTop,
  (∑ p∈window n θ,(residual p)^2)*width n ≤ K*(n:ℝ)^θ

theorem centered {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e) {β θ : ℝ}
    (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1) (ord : Ordinary β) : Second θ := by
  obtain ⟨C,hC,hc⟩ := short he ht hk hβ (hθ.trans htop).le ord
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hc
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp ((tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1)
  have hb : 0≤β := le_trans (by positivity) hβ.le
  refine ⟨32*C,by positivity,?_⟩
  filter_upwards [scales hb hθ htop 0 (show 0<(1:ℝ) by norm_num) (max Y Z)] with n hn
  obtain ⟨X,H,hX,hHX,hfit,hH,hw,hV,hcontain⟩ := hn
  have hL : 1≤log (X:ℝ) := hZ X ((le_max_right ..).trans hX)
  have hV₁ : 1≤width X := by unfold width;linarith
  have hlen : (X:ℝ)^β≤H := by
    have h₁ : 1≤(width X)^(8+0) := one_le_pow₀ hV₁
    calc _ = (X:ℝ)^β*1 := (mul_one _).symm
         _ ≤ (X:ℝ)^β*(width X)^(8+0) := mul_le_mul_of_nonneg_left h₁ (rpow_nonneg (Nat.cast_nonneg X) β)
         _ ≤ H := by simpa only [one_mul] using hfit
  have hmoment := hY X ((le_max_left ..).trans hX) H hHX hlen
  have hsub : window n θ ⊆ sample X H := by
    intro p hp
    exact ThetaShortPrimeInterval.mem_primes.mpr ⟨hcontain p hp,
      (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2,trivial⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f:=fun p => (residual p)^2) hsub (by intros; positivity)
  have hw' : width n≤4*log X := by unfold width at hw ⊢;linarith only [hw,hL]
  have h₁ := mul_le_mul_of_nonneg_left hw' (show 0≤∑ p∈window n θ,(residual p)^2 from sum_nonneg (fun p _ => sq_nonneg (residual p)))
  have h₂ := mul_le_mul_of_nonneg_right hs (show 0≤log (X:ℝ) by linarith)
  linarith only [h₁,h₂,hmoment,mul_le_mul_of_nonneg_left hH hC.le]

#print axioms short
#print axioms centered
end
end Arxiv.«2501.03234».ThetaCentralResidualBudget
