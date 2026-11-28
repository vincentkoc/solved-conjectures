import ThetaCubicEnergyLimit

/-! Removing a sublinear order range from the cubic energy. -/

namespace Arxiv.«2501.03234».ThetaSparseCubicEnergy
open Filter Finset Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaPointwiseOrders ThetaPointwiseCompletion ThetaSparseCubicMass ThetaCubicEnergy
open Asymptotics
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private lemma point (hp : _root_.Odd p) {χ : DirichletCharacter ℂ p} (hn : χ≠1) :
    ‖cubic χ‖^2 ≤ (p:ℝ)^3*(1+log p)^6 := by
  have hprime : p.Prime := Fact.out
  have hpos : 0<p/2 := Nat.div_pos hprime.two_le (by decide)
  have hh : (harmonic (p/2):ℝ)≤1+log p := (harmonic_le_one_add_log _).trans
    (add_le_add_right (log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.div_le_self p 2)) _)
  have hnon : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (harmonic_pos hpos.ne').le
  have h := (cubic_bound hp χ hn).trans (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left hh (sqrt_nonneg _)) 3)
  apply (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq
  rw [←pow_mul,mul_pow,show 3*2=2*3 by decide,(pow_mul (sqrt p) 2 3),sq_sqrt (Nat.cast_nonneg p)]

theorem negligible {ε b : ℝ} (he : 0<ε) (hb : 0<b) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      total (low p ε) ≤ b*(p:ℝ)^4 := by
  let δ := ε/14
  have hd : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hdv⟩ := divisor_bound hd
  have hl := (isLittleO_log_rpow_atTop hd).bound (by norm_num : (0:ℝ)<1)
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0<ε/2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (64*C)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const hb,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hl,
    eventually_ge_atTop 2] with p hsmall hlog hp
  intro hp' ho
  have : Fact p.Prime := ⟨hp'⟩
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
  have hsum := sum_le_sum (s:=low p ε) (fun χ hχ => point ho (mem_filter.mp (mem_filter.mp hχ).1).2)
  simp only [sum_const,nsmul_eq_mul] at hsum
  change 64*C*(p:ℝ)^(-(ε/2))≤b at hsmall
  have hlog0 := log_nonneg hx1
  have heq : (p:ℝ)^(1-ε)*(p:ℝ)^δ*((p:ℝ)^δ)^6 = (p:ℝ)^(-(ε/2))*p := by
    rw [← rpow_mul_natCast hx.le, ← rpow_add hx, ← rpow_add hx]
    rw [show (1-ε+δ+δ*(6:ℕ))=-(ε/2)+1 by dsimp [δ]; ring,
      rpow_add hx,rpow_one]
  calc
    total (low p ε) ≤ _ := hsum
    _ ≤ ((p:ℝ)^(1-ε)*(C*(p:ℝ)^δ))*((p:ℝ)^3*(2*(p:ℝ)^δ)^6) := by
      apply mul_le_mul (hc.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))) _ (by positivity) (by positivity)
      gcongr
    _ = (64*C*(p:ℝ)^(-(ε/2)))*(p:ℝ)^4 := by
      linear_combination 64*C*(p:ℝ)^3*heq
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)

#print axioms negligible
end
end Arxiv.«2501.03234».ThetaSparseCubicEnergy
