import ThetaWeilShortIntervals

/-! The original theta sum in an interval of Baker--Harman--Pintz length. -/
namespace Arxiv.«2501.03234».ThetaBHPIntervals
open Finset Real Filter ThetaShortPrimeInterval ThetaStrongDeviation ThetaStrongOriginalTail
open ThetaWeilShortIntervals (Weil)
noncomputable section

def length (X : ℕ) := ⌊(X:ℝ)^(21/40:ℝ)⌋₊

/-- Ordinary prime count at length x^0.525, separated from the theta transfer. -/
def PrimeCount : Prop := ∀ᶠ X : ℕ in atTop,
    (9/100:ℝ)*(X:ℝ)^(21/40:ℝ)/log X≤(Nat.primeCounting (X+length X)-Nat.primeCounting X:ℕ)

private theorem length_bounds : ∀ᶠ X : ℕ in atTop,
    sqrt X*exp (rate X/512)≤length X ∧ length X≤X := by
  let a : ℝ := 1/2+1/512
  let b : ℝ := 21/40-a
  have hb : 0<b := by dsimp [b,a];norm_num
  have hsmall := (tendsto_rpow_atTop hb).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hlog.eventually_ge_atTop 1,hsmall.eventually_ge_atTop 2,eventually_ge_atTop 1] with X hL h2 hX
  change 1≤log (X:ℝ) at hL
  change 2≤(X:ℝ)^b at h2
  have hx : 1≤(X:ℝ) := by exact_mod_cast hX
  have hx' : 0<(X:ℝ) := by linarith
  have he : exp (rate X/512)≤(X:ℝ)^(1/512:ℝ) := by
    rw [rpow_def_of_pos hx']
    apply exp_le_exp.mpr
    linarith only [rate_le hL]
  have hsmall' : sqrt X*exp (rate X/512)≤(X:ℝ)^a := by
    rw [sqrt_eq_rpow,show (X:ℝ)^a=(X:ℝ)^(1/2:ℝ)*(X:ℝ)^(1/512:ℝ) from rpow_add hx' _ _]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hpow := one_le_rpow hx (by dsimp [a];norm_num : 0≤a)
  have hfac := mul_le_mul_of_nonneg_left h2 (show 0≤(X:ℝ)^a by positivity)
  rw [←rpow_add hx',show a+b=21/40 by dsimp [b];ring] at hfac
  have hf := Nat.lt_floor_add_one ((X:ℝ)^(21/40:ℝ))
  have hh := Nat.floor_le (rpow_nonneg hx'.le (21/40:ℝ))
  refine ⟨hsmall'.trans ?_,?_⟩
  · change _≤(⌊(X:ℝ)^(21/40:ℝ)⌋₊:ℝ)
    have hle : (X:ℝ)^a+1≤(X:ℝ)^(21/40:ℝ) := (show (X:ℝ)^a+1≤(X:ℝ)^a*2 by linarith only [hpow]).trans hfac
    exact (lt_of_add_lt_add_right (hle.trans_lt hf)).le
  · apply Nat.cast_le (α:=ℝ) |>.mp
    exact hh.trans ((rpow_le_rpow_of_exponent_le hx (by norm_num : (21/40:ℝ)≤1)).trans_eq (rpow_one _))

/-- Every fraction below the published ordinary-prime constant survives. -/
theorem positive (weil : Weil) (bhp : PrimeCount) {c γ : ℝ} (hc : c<1/2) (hγ : γ<9/100) :
    ∀ᶠ X : ℕ in atTop, γ*(X:ℝ)^(21/40:ℝ)/log X≤
      ((primes X (length X) (fun p => c*p*log p<(S p:ℝ))).card:ℝ) := by
  let δ := 9/100-γ
  have hd : 0<δ := sub_pos.mpr hγ
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ThetaWeilShortIntervals.lower weil hc,bhp,length_bounds,hlog.eventually_ge_atTop 1,
    absorb_log_power (by positivity : 0<1/δ) (by norm_num : (0:ℝ)<2048) 0] with X hlo hcount hlen hl hdec
  obtain ⟨hs,hHX⟩ := hlen
  change 1≤log (X:ℝ) at hl
  have hl' : 0≤log (X:ℝ) := by linarith
  simp only [pow_zero,mul_one] at hdec
  have he : exp (-rate X/2048)≤δ := by
    rw [show -rate X/2048= -(rate X/2048) by ring,exp_neg,←one_div]
    exact (one_div_le_one_div_of_le (one_div_pos.mpr hd) hdec).trans_eq (one_div_one_div δ)
  have hbad := hlo (length X) hs hHX
  have hH : (length X:ℝ)≤(X:ℝ)^(21/40:ℝ) := Nat.floor_le (by positivity)
  have hbad' := hbad.trans (mul_le_mul (div_le_div_of_nonneg_right hH hl') he (exp_pos _).le
    (by positivity))
  have cover : primes X (length X) (fun _ => True)⊆
      primes X (length X) (fun p => (S p:ℝ)≤c*p*log p) ∪ primes X (length X) (fun p => c*p*log p<(S p:ℝ)) := by
    intro p hp
    obtain ⟨hi,hp,_⟩ := mem_primes.mp hp
    rcases le_or_gt (S p:ℝ) (c*p*log p) with h|h
    · exact mem_union_left _ (mem_primes.mpr ⟨hi,hp,h⟩)
    · exact mem_union_right _ (mem_primes.mpr ⟨hi,hp,h⟩)
  have hh := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card cover).trans (card_union_le ..))
  rw [total_count,Nat.cast_add] at hh
  have id : (9/100:ℝ)*(X:ℝ)^(21/40:ℝ)/log X=
      γ*(X:ℝ)^(21/40:ℝ)/log X+((X:ℝ)^(21/40:ℝ)/log X)*δ := by dsimp [δ];ring
  rw [id] at hcount
  linarith only [hcount,hh,hbad']

/-- Prime-normalized two-sided exception count at the exact published length. -/
theorem relative (weil : Weil) (bhp : PrimeCount) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop,
    ((primes X (length X) (fun p => ε*(p:ℝ)*log p≤|(S p:ℝ)-p*log p/2|)).card:ℝ) ≤
      (100/9:ℝ)*((Nat.primeCounting (X+length X)-Nat.primeCounting X:ℕ):ℝ)*exp (-rate X/2048) := by
  have hb := original_of_bound (ThetaWeilShortIntervals.square_root weil) hε
  filter_upwards [hb,bhp,length_bounds,eventually_ge_atTop 1] with X hbad hcount hh hX
  have hx := log_nonneg (by exact_mod_cast hX : 1≤(X:ℝ))
  have h := hbad (length X) (by simpa only [←sqrt_eq_rpow] using hh.1) hh.2
  have hfloor : (length X:ℝ)≤(X:ℝ)^(21/40:ℝ) := Nat.floor_le (by positivity)
  have hnorm : (length X:ℝ)/log X≤(100/9:ℝ)*((Nat.primeCounting (X+length X)-Nat.primeCounting X:ℕ):ℝ) := by
    apply (div_le_div_of_nonneg_right hfloor hx).trans
    have he : (9/100:ℝ)*(X:ℝ)^(21/40:ℝ)/log X = (9/100:ℝ)*((X:ℝ)^(21/40:ℝ)/log X) := by ring
    rw [he] at hcount
    linarith only [hcount]
  exact h.trans (mul_le_mul_of_nonneg_right hnorm (exp_pos _).le)

#print axioms relative

#print axioms positive
end
end Arxiv.«2501.03234».ThetaBHPIntervals
