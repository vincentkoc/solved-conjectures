import ThetaLocalVanishingCone
import ThetaLocalModelError
import ThetaPrimeResidualLaw

/-! A signed local model with vanishing deterministic error and translated
square error for the discarded denominator rows. -/
namespace Arxiv.«2501.03234».ThetaLocalCenteredApproximation
open Real Finset Filter ThetaCalibratedCone ThetaLocalVanishingCone ThetaLocalModelError
open ThetaPrimeMeanSquare ThetaDivisibleDiagonal ThetaDiagonalConstant ThetaPrimeLaw
open ThetaPrimeTailTransfer ThetaCharacterPrimeMeans ThetaNondivisibleCone ThetaPrimeDensity ThetaPrimeAsymptotic
open ThetaDenominatorTails ThetaReciprocalInversion ThetaReciprocalBlocks ThetaRowCorrelations
noncomputable section

theorem signed {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ {T p : ℕ}, T≤N → p.Prime → N^56≤p → p≤N^64 →
    let F := windowExtension (above T (coneWindow (coneWidth N))) (2*fine e N) p
    |residual p-residualModel T N p|≤ε+(8/π^2)*(3*(T:ℝ)/N+‖F‖) := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp diagonal_second_order (ε/2) (half_pos hε))
  filter_upwards [square_fit,ht.eventually_ge_atTop (9201200/ε),eventually_ge_atTop (max 2 p₀)] with N hfit hlog hN
  intro T p hTN hp hl hh F
  have hN2 := (le_max_left 2 p₀).trans hN
  have hN1 : 1≤N := by omega
  have hNp : 0<N := by omega
  have hNp' : N≤N^56 := Nat.le_self_pow (by decide) N
  have hdiag := hp₀ p ((le_max_right 2 p₀).trans (hN.trans (hNp'.trans hl)))
  rw [Real.dist_eq] at hdiag
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have ho := hp.eq_two_or_odd.resolve_left (by have := Nat.pow_le_pow_left hN2 56; omega)
  let : Fact p.Prime := ⟨hp⟩
  let J := fine e N
  let K := coneWindow (coneWidth N)
  let c := 8/π^2
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨hlo,hJ,_⟩ := bounds he h48 hN1
  have hy := (Nat.mul_le_mul_left 2 hJ).trans_lt (cutoff_inside hN2 hl)
  have hTK : T≤2*J := by have := (Nat.le_self_pow (by decide : 2≠0) N).trans hlo; dsimp only [J];omega
  let B := (rationalCone p J (coneWidth N):ℝ)
  have hcore : |residual p-(diagonalConstant+c*B)|≤ε := by
    have hf := estimate he h48 hk hN2 hfit hp hl hh
    have hL : 0<(levels N:ℝ) := by exact_mod_cast Nat.succ_pos _
    have hLE : 4600600/(levels N:ℝ)≤ε/2 := by
      change 9201200/ε≤log (N:ℝ) at hlog
      have hh := (div_le_iff₀ hε).mp (hlog.trans (levels_bounds hN1).1)
      rw [div_le_iff₀ hL]
      nlinarith only [hh]
    have hnorm : |offDiagonal p/p-c*B|≤ε/2 := by
      have H : offDiagonal p/p-c*B=(offDiagonal p-(8*p/π^2)*B)/p := by dsimp [c];field_simp
      rw [H,abs_div,abs_of_pos hpr]
      apply (div_le_div_of_nonneg_right hf hpr.le).trans
      calc _ = 4600600/(levels N:ℝ) := by field_simp
           _ ≤ _ := hLE
    have heq : residual p-(diagonalConstant+c*B)=
        (divisibleDiagonal p/p-log p/2-diagonalConstant)+(offDiagonal p/p-c*B) := by
      rw [ThetaCharacterPrimeMeans.residual,S_eq_diagonal_add_offDiagonal ho,add_div];ring
    rw [heq]
    exact (abs_add_le ..).trans (by linarith only [hdiag,hnorm])
  have hu (d : ℕ) (hd : d∈Icc 1 (2*J)) : p.Coprime d := hp.coprime_iff_not_dvd.mpr
    (fun hv => ((mem_Icc.mp hd).2.trans_lt hy).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 hv))
  have hs := window_split hTK K (by simp [K,coneWindow]) hu
  rw [cone_interpolation (show coneWidth N%2=1 by unfold coneWidth;omega) hp hy] at hs
  let V := low T K (commonWeight (2*J)) p
  have hb : |B-V|=‖F‖ := by
    rw [←Real.norm_eq_abs,←Complex.norm_real,Complex.ofReal_sub]
    congr 1
    change (↑(↑(rationalCone p J (coneWidth N)):ℝ):ℂ)-_=_
    rw [Complex.ofReal_ratCast]
    change (rationalCone p J (coneWidth N):ℂ)-_= (V:ℂ) at hs
    linear_combination hs

  have hswap : |model T N p-V|≤3*(T:ℝ)/N := swap_ratio hNp hTN
    (hlo.trans (by omega)) (Nat.mul_le_mul_left 2 hJ) K p
  have hd := (abs_sub_le B V (model T N p)).trans (add_le_add hb.le ((abs_sub_comm ..).le.trans hswap))
  have h := abs_sub_le (residual p) (diagonalConstant+c*B) (residualModel T N p)
  rw [residualModel,show diagonalConstant+c*B-(diagonalConstant+8/π^2*model T N p)=c*(B-model T N p) by dsimp [c];ring,abs_mul,abs_of_pos hc] at h
  apply h.trans
  rw [add_comm ‖F‖] at hd
  exact add_le_add hcore (mul_le_mul_of_nonneg_left hd hc.le)

#print axioms signed
end
end Arxiv.«2501.03234».ThetaLocalCenteredApproximation
