import Erdos478MixedParityTradeoff
import Erdos478MixedProductCoverage

/-! # Quantitative lower bounds from the mixed factorial product image -/

namespace Erdos478.ParityProducts
open Finset Filter Real Asymptotics
open Arxiv.«2501.03234».ThetaReciprocalCutoff (discrepancy)
noncomputable section

/-- The exact positive-index image in the pinned Erdős 478 limit. -/
def imageSize (p : ℕ) := ((Ico 1 p).image (fun i => i.factorial%p)).card

theorem uniform_value_bound {p : ℕ} [Fact p.Prime] (hp : p%2=1) :
    32*p ≤ 21*(imageSize p)^2+24*imageSize p+16 := by
  have cap := mixed_capacity hp
  change 16*(mixedProducts p).card≤7*(imageSize p)^2+8*imageSize p at cap
  have cover := mixed_pointwise hp
  omega

theorem discrepancy_value_bound {p : ℕ} [Fact p.Prime] (hp : p%2=1) :
    12*((p:ℝ)-1) ≤ 7*(imageSize p:ℝ)^2+8*(imageSize p:ℝ)+8*discrepancy p := by
  have cap : 16*((mixedProducts p).card:ℝ)≤7*(imageSize p:ℝ)^2+8*(imageSize p:ℝ) := by
    exact_mod_cast mixed_capacity hp
  linarith only [cap,mixed_discrepancy hp]

/-- The explicit error from the reciprocal-parity estimate is o(p). -/
theorem relative_discrepancy (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ p : ℕ in atTop, discrepancy p≤ε*p := by
  have small : (fun p : ℕ => (log p)^2) =o[atTop] (fun p : ℕ => (p:ℝ)^(1/4:ℝ)) := by
    simpa only [rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/4)).natCast_atTop
  filter_upwards [small.bound (show 0<ε/36 by positivity),eventually_ge_atTop (3:ℕ)] with p hg hp
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have pos : (0:ℝ)<p := by linarith
  have loglarge : 1≤log p := (le_log_iff_exp_le pos).mpr (exp_one_lt_three.le.trans hp')
  have hh : (harmonic (p/2):ℝ)≤1+log p := (harmonic_le_one_add_log _).trans
    (add_le_add_right (log_le_log (by exact_mod_cast (show 0<p/2 by omega)) (by exact_mod_cast Nat.div_le_self p 2)) _)
  have hnon : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (harmonic_pos (by omega : p/2≠0)).le
  have sq : (1+(harmonic (p/2):ℝ))^2 ≤ 9*(log p)^2 := by
    calc
      _≤(3*log p)^2 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _=_ := by ring
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log (p:ℝ))),abs_of_pos (rpow_pos_of_pos pos _)] at hg
  have cancel : (p:ℝ)^(3/4:ℝ)*(p:ℝ)^(1/4:ℝ)=p := by rw [← rpow_add pos]; norm_num
  unfold discrepancy
  calc
    _ ≤ 4*(p:ℝ)^(3/4:ℝ)*(9*((ε/36)*(p:ℝ)^(1/4:ℝ))) := by gcongr; exact sq.trans (by gcongr)
    _ = ε*((p:ℝ)^(3/4:ℝ)*(p:ℝ)^(1/4:ℝ)) := by ring
    _ = _ := by rw [cancel]

/-- Every coefficient below sqrt(12/7) works for every sufficiently large prime. -/
theorem eventual_value_bound (c : ℝ) (hc : 0≤c) (hgap : 7*c^2<12) :
    ∀ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime}, c*sqrt p≤(imageSize p:ℝ) := by
  let δ := (12-7*c^2)/32
  have pos : 0<δ := by dsimp [δ]; linarith
  have grow := tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have bound := grow.eventually_ge_atTop ((8*c+12)/δ)
  rw [eventually_inf_principal]
  filter_upwards [relative_discrepancy δ pos,bound,eventually_ge_atTop (3:ℕ)] with p herr hs hp prime
  have pr : p.Prime := prime
  let : Fact p.Prime := ⟨pr⟩
  have odd : p%2=1 := Nat.odd_iff.mp (pr.odd_of_ne_two (by omega))
  have pp : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have root := sq_sqrt pp.le
  have sr : 1≤ sqrt p := by simpa using sqrt_le_sqrt (show (1:ℝ)≤p by exact_mod_cast (show 1≤p by omega))
  have hs' : 8*c+12 ≤ δ*sqrt p := by simpa [mul_comm] using (div_le_iff₀ pos).mp hs
  have room : (8*c+12)*sqrt p≤δ*p := by nlinarith only [mul_le_mul_of_nonneg_right hs' (sqrt_nonneg (p:ℝ)),congrArg (δ*·) root]
  by_contra! low
  have sq := sq_le_sq₀ (by positivity : 0≤(imageSize p:ℝ)) (mul_nonneg hc (sqrt_nonneg (p:ℝ)))
  have top := (sq.mpr low.le)
  have q : (c*sqrt p)^2=c^2*p := by rw [mul_pow,root]
  rw [q] at top
  have main := discrepancy_value_bound odd
  have eh : 12*(p:ℝ) = 7*c^2*p+32*δ*p := by dsimp [δ]; ring
  nlinarith only [main,top,low.le,herr,room,sr,eh,mul_pos pos pp]

#print axioms imageSize
#print axioms uniform_value_bound
#print axioms discrepancy_value_bound
#print axioms relative_discrepancy
#print axioms eventual_value_bound
end
end Erdos478.ParityProducts
