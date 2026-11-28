import ThetaWorstPrimeClasses
import ThetaShortPrimeInterval

/-! Worst-class bounds simultaneously in every polynomially short interval. -/
namespace Arxiv.«2501.03234».ThetaShortIntervalClasses
open Filter Finset Real ThetaStrongDeviation ThetaStrongOriginalTail ThetaShortPrimeInterval ThetaWorstPrimeClasses
noncomputable section

def saving (X : ℕ) := rate X/16384

theorem of_count {θ : ℝ} {P : ℕ → Prop} (hP : ∀ᶠ X : ℕ in atTop,∀ H : ℕ,
    (X:ℝ)^θ*exp (rate X/512)≤H → H≤X →
      ((primes X H P).card:ℝ) ≤ (H:ℝ)/log X*exp (-rate X/2048)) :
    ∀ᶠ X : ℕ in atTop,∀ H : ℕ,(X:ℝ)^θ*exp (rate X/512)≤H → H≤X →
      ∀ Q : ℕ,(Q:ℝ)^2≤H*exp (saving X) →
      total (primes X H P) Q ≤ (H:ℝ)/log X*exp (-(2*saving X)) := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hl := tendsto_log_atTop.comp hn
  filter_upwards [hP,absorb_log_power (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<16384) 3,
    hl.eventually_ge_atTop 4,hn.eventually_gt_atTop 0] with X hC hcube hL hx H hH hsmall Q hQ
  let s := saving X
  let L := log (X:ℝ)
  change 4≤L at hL
  have hp : 0<L := by linarith
  change 1*(1+L)^3≤ exp s at hcube
  rw [one_mul] at hcube
  have hLe : L ≤ exp s := (show L ≤ (1+L)^3 by nlinarith only [hL,pow_le_pow_right₀ (show 1≤1+L by linarith) (by decide : 1≤3)]).trans hcube
  have h1 : 1≤ s := by
    apply le_of_not_gt;intro he
    have hh := (exp_lt_exp.mpr he).trans exp_one_lt_d9
    linarith only [hL,hLe,hh]
  have hr : 0≤ rate X := sqrt_nonneg _
  have hsL : s≤L := (div_le_self hr (by norm_num : (1:ℝ)≤16384)).trans (rate_le (by linarith : 1≤L))
  have hQX : (Q:ℝ)≤X := by
    have he := exp_le_exp.mpr hsL;rw [exp_log hx] at he
    have hsq := hQ.trans (mul_le_mul (Nat.cast_le.mpr hsmall) he (exp_pos _).le hx.le)
    exact le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) hx.le (by simpa only [sq] using hsq)
  have hlog : log (Q:ℝ) ≤ L := by
    by_cases h : Q=0
    · simp only [h,Nat.cast_zero,log_zero];linarith only [hL]
    · exact log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) hQX
  have hsum : (ThetaProgressionIncidence.harmonicSum Q)^3 ≤ exp s := by
    have h := (ThetaProgressionIncidence.harmonic_bound Q).trans (add_le_add le_rfl hlog)
    have hn : 0≤ThetaProgressionIncidence.harmonicSum Q := sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
    exact (pow_le_pow_left₀ hn h _).trans hcube
  have hcount := hC H hH hsmall
  have he : ((primes X H P).card:ℝ) ≤ (H:ℝ)/L*exp (-(8*s)) := by
    have ha : -rate X/2048= -(8*s) := by dsimp [s,saving];ring
    rw [ha] at hcount;exact hcount
  have hmain : (H:ℝ)≤(H:ℝ)/L*exp s := by
    calc _ = (H:ℝ)/L*L := (div_mul_cancel₀ _ hp.ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left hLe (div_nonneg (Nat.cast_nonneg H) hp.le)
  exact sparse (u:=X) (div_nonneg (Nat.cast_nonneg H) hp.le) h1 (fun p hp =>
    let h := mem_Ioc.mp (mem_primes.mp hp).1
    ⟨h.1.le,h.2⟩) he hQ hsum hmain

theorem centered {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop,∀ H : ℕ,
    (X:ℝ)^(3/4:ℝ)*exp (rate X/512)≤H → H≤X → ∀ Q : ℕ,(Q:ℝ)^2≤H*exp (saving X) →
    total (primes X H (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)) Q ≤
      (H:ℝ)/log X*exp (-(2*saving X)) := of_count (ThetaShortPrimeInterval.original hε)

theorem slope {c : ℝ} (hc : c<1/2) : ∀ᶠ X : ℕ in atTop,∀ H : ℕ,
    (X:ℝ)^(3/4:ℝ)*exp (rate X/512)≤H → H≤X → ∀ Q : ℕ,(Q:ℝ)^2≤H*exp (saving X) →
    total (primes X H (fun p => (S p:ℝ)≤ c*p*log p)) Q ≤ (H:ℝ)/log X*exp (-(2*saving X)) :=
  of_count (ThetaShortPrimeInterval.lower hc)

#print axioms of_count
#print axioms centered
#print axioms slope
end
end Arxiv.«2501.03234».ThetaShortIntervalClasses
