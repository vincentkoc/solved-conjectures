import ThetaAbsoluteCubicMass

/-! Sublinear-order characters carry negligible absolute cubic mass on the p^(5/2) scale. -/
namespace Arxiv.«2501.03234».ThetaSparseCubicMass
open Finset Filter Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCompletion ThetaPointwiseCutoff
open ThetaPointwiseOrders ThetaAbsoluteCubicMass
open scoped Topology
noncomputable section

def low (p : ℕ) [Fact p.Prime] (ε : ℝ) :=
  (nonprincipal p).filter (fun χ => (orderOf χ:ℝ)≤(p:ℝ)^(1-ε))

theorem term {p : ℕ} [Fact p.Prime] (hp : _root_.Odd p) {χ : DirichletCharacter ℂ p} (hn : χ≠1) :
    |(cubic χ).re| ≤ (Real.sqrt p*(1+log p))^3 := by
  have hprime : p.Prime := Fact.out
  have hH : 0 < p/2 := Nat.div_pos hprime.two_le (by decide)
  have hh : (harmonic (p/2):ℝ)≤1+log p := (harmonic_le_one_add_log _).trans
    (add_le_add_right (log_le_log (by exact_mod_cast hH) (by exact_mod_cast Nat.div_le_self p 2)) _)
  have hnon : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (harmonic_pos hH.ne').le
  exact (Complex.abs_re_le_norm _).trans ((cubic_bound hp χ hn).trans (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)) _))

theorem negligible {ε b : ℝ} (he : 0<ε) (hb : 0<b) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      mass (low p ε) ≤ b*scale p := by
  let δ := ε/8
  have hd : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hdv⟩ := divisor_bound hd
  have hl := (isLittleO_log_rpow_atTop hd).bound (by norm_num : (0:ℝ)<1)
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0< ε/2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (8*C)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const hb,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hl,
    eventually_ge_atTop 2] with p hsmall hlog hp
  intro hp' ho
  let : Fact p.Prime := ⟨hp'⟩
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp'.pos
  have hx1 : 1≤(p:ℝ) := by exact_mod_cast hp'.pos
  have hr := rpow_pos_of_pos hx δ
  simp only [Real.norm_eq_abs,abs_of_nonneg (log_nonneg hx1),abs_of_pos hr,one_mul] at hlog
  have hlp : 1+log p≤2*(p:ℝ)^δ := by linarith [one_le_rpow hx1 hd.le]
  have hdiv : ((p-1).divisors.card:ℝ)≤C*(p:ℝ)^δ :=
    (hdv (p-1) (by omega)).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le p 1)) hd.le) hC.le)
  have hc := count_orders ho ((p:ℝ)^(1-ε)) (rpow_nonneg hx.le _) (low p ε)
    (fun _ h => (mem_filter.mp h).2)
  have H := sum_le_sum (s:=low p ε) (fun χ hχ => term ho (mem_filter.mp (mem_filter.mp hχ).1).2)
  simp only [sum_const,nsmul_eq_mul] at H
  change 8*C*(p:ℝ)^(-(ε/2))≤b at hsmall
  have hlog0 := log_nonneg hx1
  calc mass (low p ε) ≤ _ := H
       _ ≤ ((p:ℝ)^(1-ε)*(C*(p:ℝ)^δ))*(Real.sqrt p*(2*(p:ℝ)^δ))^3 := by
         apply mul_le_mul (hc.trans (mul_le_mul_of_nonneg_left hdiv (rpow_nonneg hx.le _)))
           (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hlp (Real.sqrt_nonneg _)) _) (by positivity) (by positivity)
       _ = (8*C*(p:ℝ)^(-(ε/2)))*scale p := by
         unfold scale
         have Hpow : (p:ℝ)^(1-ε)*(p:ℝ)^δ*(p:ℝ)^δ*(p:ℝ)^δ*(p:ℝ)^δ =
             (p:ℝ)^(-(ε/2))*p := by
           calc _ = (p:ℝ)^(-(ε/2))*(p:ℝ)^(1:ℝ) := by
                  simp only [←rpow_add hx]; congr 1; dsimp [δ]; ring
                _ = _ := by rw [rpow_one]
         nlinarith only [congrArg (fun z : ℝ => 8*C*z*Real.sqrt p*(p:ℝ)) Hpow,
           congrArg (fun z : ℝ => 8*C*(p:ℝ)^(1-ε)*((p:ℝ)^δ)^4*Real.sqrt p*z) (Real.sq_sqrt hx.le)]
       _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by unfold scale; positivity)

#print axioms negligible
end
end Arxiv.«2501.03234».ThetaSparseCubicMass
