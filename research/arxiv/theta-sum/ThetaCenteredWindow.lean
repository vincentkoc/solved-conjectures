import ThetaOrbitProjection

/-! Exponential concentration around the multiplicative orbit projection on all residues. -/
namespace Arxiv.«2501.03234».ThetaCenteredWindow
open Finset Real Filter ThetaAllWindowMoments ThetaOrbitProjection ThetaSmoothConditionalModel
open ThetaConditionalRows ThetaPeriodMeans ThetaTiltBudget ThetaRowCorrelations
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩

theorem smooth_periodic {d : ℕ} {f : ℕ → ℝ} (hf : OnMod d f) (Y T : ℕ) :
    OnMod d (smooth Y T f) := by
  intro n
  unfold smooth ThetaFiniteExposure.avg
  congr 1
  apply sum_congr rfl
  intro u _
  let t := (u:ZMod Y.factorial).val
  calc f (n%d*t) = f ((n%d*t)%d) := (hf _).symm
       _ = f ((n*t)%d) := congrArg f (by simp [Nat.mul_mod])
       _ = _ := hf _

def center (Y T : ℕ) (W : Window) (n : ℕ) := rowModel Y W n-smooth Y T (rowModel Y W) n

theorem center_mod (Y T : ℕ) (W : Window) : OnMod Y.factorial (center Y T W) := by
  intro n
  dsimp only [center]
  rw [periodic Y W n,smooth_periodic (periodic Y W) Y T n]

theorem signed : ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (W : Window) (v : ℝ), |v|=tilt T →
    mean Y.factorial (fun n => exp (v*center Y T W n)) ≤ exp total := by
  classical
  filter_upwards [ThetaCenteredExposure.centered_mgf] with T H
  intro Y W a ha
  let Q := Y.factorial
  let f (x : ZMod Q) := exp (a*center Y T W x.val)
  have ht : 0<(Q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _))
  have hQ : 0<(Q:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hf (x : ZMod Q) : ∑ u : (ZMod Q)ˣ,f ((u:ZMod Q)*x)≤exp total*Q.totient := by
    obtain ⟨v,hv⟩ := orbit Y T x.val W
    let g (u : (ZMod Q)ˣ) := exp (a*center Y T (masked W x.val) (u:ZMod Q).val)
    have he (u : (ZMod Q)ˣ) : f ((u:ZMod Q)*x)=g (v*u) := by
      dsimp only [f,g,Units.val_mul]
      rw [mul_comm (u:ZMod Q) x,ZMod.val_mul,ZMod.val_mul,
        center_mod Y T W _,center_mod Y T (masked W x.val) _]
      unfold center
      rw [(hv _).1,(hv _).2]
    simp_rw [he]
    rw [show (∑ u : (ZMod Q)ˣ,g (v*u))=∑ u,g u from
      Fintype.sum_bijective _ (Equiv.mulLeft v).bijective _ _ (fun _ => rfl)]
    simpa only [g,center,unit_value] using H Y (masked W x.val) a ha
  have hs := sum_le_sum (s:=univ) (fun x (_ : x∈(univ : Finset (ZMod Q))) => hf x)
  rw [sum_comm] at hs
  have he (u : (ZMod Q)ˣ) : (∑ x : ZMod Q, f ((u:ZMod Q)*x))=∑ x,f x :=
    Fintype.sum_bijective _ (Units.mulLeft u).bijective _ _ (fun _ => rfl)
  simp only [he,sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient,ZMod.card] at hs
  unfold mean
  rw [ThetaAllWindowMoments.sum_period,div_le_iff₀ hQ]
  change ∑ x : ZMod Q,f x ≤ exp total*Q
  exact (mul_le_mul_iff_right₀ ht).mp (by linarith only [hs])

theorem absolute : ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (W : Window),
    mean Y.factorial (fun n => exp (tilt T*|center Y T W n|)) ≤ 2*exp total := by
  filter_upwards [signed,eventually_ge_atTop 1] with T h hT
  intro Y W
  have ha := tilt_pos hT
  have hp := h Y W (tilt T) (abs_of_pos ha)
  have hn := h Y W (-(tilt T)) (by rw [abs_neg,abs_of_pos ha])
  have he (z : ℝ) : exp (tilt T*|z|)≤exp (tilt T*z)+exp ((-(tilt T))*z) := by
    rcases le_total 0 z with hz|hz
    · rw [abs_of_nonneg hz];linarith only [exp_pos ((-tilt T)*z)]
    · rw [abs_of_nonpos hz,mul_neg,← neg_mul];linarith only [exp_pos (tilt T*z)]
  have hs := sum_le_sum (s:=range Y.factorial) (fun n _ => he (center Y T W n))
  rw [sum_add_distrib] at hs
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg Y.factorial (α:=ℝ))
  rw [add_div] at hh
  unfold mean at *
  linarith only [hh,hp,hn]

#print axioms absolute
end
end Arxiv.«2501.03234».ThetaCenteredWindow
