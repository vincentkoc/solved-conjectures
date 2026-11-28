import ThetaCenteredMoment
import ThetaPrimeSieve

/-! Sieve weights preserve the centered exponential moment on every unit orbit. -/
namespace Arxiv.«2501.03234».ThetaSievedOrbitMoments
open Real Filter Finset ThetaPeriodMeans ThetaPrimeSieve ThetaAllWindowMoments ThetaCenteredWindow
open ThetaSmoothConditionalModel ThetaOrbitProjection ThetaConditionalRows ThetaTiltBudget
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩

theorem orbit_signed : ∀ᶠ T : ℕ in atTop, ∀ Y n : ℕ, ∀ W : Window, ∀ a : ℝ, |a|=tilt T →
    unitMean Y.factorial (fun u => exp (a*center Y T W (n*u)))≤exp total := by
  filter_upwards [ThetaCenteredExposure.centered_mgf] with T H
  intro Y n W a ha
  let Q := Y.factorial
  have ht : 0<(Q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _))
  obtain ⟨v,hv⟩ := orbit Y T n W
  let g (u : (ZMod Q)ˣ) := exp (a*center Y T (masked W n) (u:ZMod Q).val)
  have he (u : (ZMod Q)ˣ) : exp (a*center Y T W (n*(u:ZMod Q).val))=g (v*u) := by
    dsimp only [g,Units.val_mul]
    rw [ZMod.val_mul,center_mod Y T (masked W n) _]
    unfold center
    rw [(hv _).1,(hv _).2]
  unfold unitMean
  rw [div_le_iff₀ ht]
  simp_rw [he]
  rw [show (∑ u : (ZMod Q)ˣ,g (v*u))=∑ u,g u from
    Fintype.sum_bijective _ (Equiv.mulLeft v).bijective _ _ (fun _ => rfl)]
  simpa only [g,center,unit_value] using H Y (masked W n) a ha

/-- A uniform bound on every multiplicative orbit survives multiplication by
any nonnegative weight constant on the orbits. The average is over all residues. -/
theorem weighted_mean {P : ℕ} (hp : 0<P) {w f : ℕ → ℝ} {K : ℝ} (hw : ∀ n, 0≤w n)
    (hi : ∀ (u : (ZMod P)ˣ) (x : ZMod P), w ((u:ZMod P)*x).val=w x.val)
    (hper : OnMod P f) (horb : ∀ n, @unitMean P ⟨hp.ne'⟩ (fun t => f (n*t))≤K) :
    mean P (fun n => w n*f n)≤K*mean P w := by
  classical
  let : NeZero P := ⟨hp.ne'⟩
  have ht : 0<(P.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hp)
  have hP : 0<(P:ℝ) := Nat.cast_pos.mpr hp
  let F (u : (ZMod P)ˣ) (x : ZMod P) := w ((u:ZMod P)*x).val*f ((u:ZMod P)*x).val
  have hx (x : ZMod P) : ∑ u : (ZMod P)ˣ,F u x ≤w x.val*(K*P.totient) := by
    have ho := (div_le_iff₀ ht).mp (horb x.val)
    apply le_trans _ (mul_le_mul_of_nonneg_left ho (hw _))
    rw [mul_sum]
    apply sum_le_sum
    intro u _
    change w ((u:ZMod P)*x).val*f ((u:ZMod P)*x).val≤_
    rw [hi,mul_comm (u:ZMod P) x,ZMod.val_mul,hper]
  have hsum := sum_le_sum (s:=univ) (fun x (_ : x∈(univ : Finset (ZMod P))) => hx x)
  rw [sum_comm,←sum_mul] at hsum
  have he (u : (ZMod P)ˣ) : (∑ x : ZMod P,F u x)=∑ x : ZMod P,w x.val*f x.val :=
    Fintype.sum_bijective _ (Units.mulLeft u).bijective _ _ (fun _ => rfl)
  simp only [he,sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient] at hsum
  unfold mean
  rw [sum_period,sum_period,←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hP.le
  exact (mul_le_mul_iff_right₀ ht).mp (by linarith only [hsum])

theorem signed : ∀ᶠ T : ℕ in atTop, ∀ (Y R : ℕ), 1≤R → Y≤R → ∀ (W : Window) (a : ℝ),
    |a|=tilt T → mean R.factorial (fun n => weight R n*exp (a*center Y T W n))≤
      exp total*(normalizer R)⁻¹ := by
  filter_upwards [orbit_signed] with T H
  intro Y R hR hYR W a ha
  have hr (r : ℕ) (hr : r∈moduli R) := Nat.dvd_factorial (mem_Icc.mp (mem_filter.mp hr).1).1 (mem_Icc.mp (mem_filter.mp hr).1).2
  have hd : Y.factorial∣R.factorial := Nat.factorial_dvd_factorial hYR
  let f (n : ℕ) := exp (a*center Y T W n)
  have hf : OnMod Y.factorial f := fun n => by dsimp [f];rw [center_mod]
  rw [←mean_weight hR (Nat.factorial_pos _) hr]
  apply weighted_mean (Nat.factorial_pos _) (f:=f) (fun _ => sq_nonneg _) (weight_invariant hr) (onMod_lift hd hf)
  intro n
  have hper : OnMod Y.factorial (fun u => f (n*u)) := by
    intro u
    change f (n*(u%Y.factorial))=f (n*u)
    rw [←hf (n*(u%Y.factorial)),Nat.mul_mod_mod,hf]
  rw [unitMean_lift hd hper]
  exact H Y n W a ha

theorem absolute : ∀ᶠ T : ℕ in atTop, ∀ Y R : ℕ, 1≤R → Y≤R → ∀ W : Window,
    mean R.factorial (fun n => weight R n*exp (tilt T*|center Y T W n|))≤
      (2*exp total)*(normalizer R)⁻¹ := by
  filter_upwards [signed,eventually_ge_atTop 1] with T H hT
  intro Y R hR hYR W
  have ha := tilt_pos hT
  have hp := H Y R hR hYR W (tilt T) (abs_of_pos ha)
  have hn := H Y R hR hYR W (-(tilt T)) (by rw [abs_neg,abs_of_pos ha])
  have he (z : ℝ) : exp (tilt T*|z|)≤exp (tilt T*z)+exp ((-(tilt T))*z) := by
    rcases le_total 0 z with hz|hz
    · rw [abs_of_nonneg hz];linarith only [exp_pos ((-tilt T)*z)]
    · rw [abs_of_nonpos hz,mul_neg,←neg_mul];linarith only [exp_pos (tilt T*z)]
  have hh := sum_le_sum (s:=range R.factorial) (fun n _ => mul_le_mul_of_nonneg_left (he (center Y T W n)) (show 0≤weight R n from sq_nonneg _))
  change (∑ n∈range R.factorial,weight R n*_)≤∑ n∈range R.factorial,weight R n*(_+_) at hh
  simp only [mul_add,sum_add_distrib] at hh
  have hdiv := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) R.factorial)
  rw [add_div] at hdiv
  unfold mean at *
  linarith only [hdiv,hp,hn]

#print axioms weighted_mean
#print axioms absolute
end
end Arxiv.«2501.03234».ThetaSievedOrbitMoments
