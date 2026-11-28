import ThetaSievedConcentration
import ThetaPrimeTailTransfer

/-! Quadratic approximation to the signed residual on an arbitrary prime subfamily. -/
namespace Arxiv.«2501.03234».ThetaMovingPrimeModelError
open Real Finset ThetaPrimeTailTransfer ThetaPrimeMeanSquare ThetaNondivisibleCone
open ThetaDivisibleDiagonal ThetaPrimeDensity ThetaReciprocalInversion ThetaDenominatorTails
open ThetaRowCorrelations ThetaPrimeAsymptotic
noncomputable section

private theorem signed : ∃ D : ℝ, 0<D ∧ ∀ {N T p : ℕ}, 2≤N → T≤N →
    p.Prime → N^56≤p → p≤N^64 →
    |(S p:ℝ)/p-log p/2-(8/Real.pi^2)*model T N p| ≤
      D+(8/Real.pi^2)*‖windowExtension (above T (coneWindow (coneWidth N))) (2*N^52) p‖ := by
  obtain ⟨C,hC,h⟩ := S_sub_offDiagonal_asymptotic
  refine ⟨C+2265902,by positivity,?_⟩
  intro N T p hN hT hp hl hh
  let : Fact p.Prime := ⟨hp⟩
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hy := cutoff_inside hN hl
  have ho := hp.eq_two_or_odd.resolve_left (by have := Nat.one_le_pow 52 N (by omega); omega)
  have hdiag : |(S p:ℝ)/p-log p/2-offDiagonal p/p|≤C := by
    have H := div_le_div_of_nonneg_right (h p ho) hpR.le
    rwa [←abs_of_pos hpR,←abs_div,abs_of_pos hpR,mul_div_cancel_right₀ _ hpR.ne',
      show ((S p:ℝ)-offDiagonal p-p*log p/2)/p=(S p:ℝ)/p-log p/2-offDiagonal p/p by field_simp; ring] at H
  have he := normalized_cone_error hN hp hl hh
  have hb : (2265642+4*(1+64*log N))/N≤2265902 := by
    apply (div_le_iff₀ hn).mpr
    have h1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    linarith [log_le_self hn.le]
  let L := coneWindow (coneWidth N)
  let F := windowExtension (above T L) (2*N^52) p
  have hu (d : ℕ) (hd : d∈Icc 1 (2*N^52)) : p.Coprime d := hp.coprime_iff_not_dvd.mpr
    (fun hdv => ((mem_Icc.mp hd).2.trans_lt hy).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 hdv))
  have hcap : T≤2*N^52 := by have := Nat.le_self_pow (by decide : 52≠0) N; omega
  have hs := window_split hcap L (by simp [L,coneWindow]) hu
  rw [cone_interpolation (show coneWidth N%2=1 by unfold coneWidth; omega) hp hy] at hs
  have heq : ((↑(rationalCone p (N^52) (coneWidth N)):ℝ):ℂ)-(model T N p:ℂ)=F := by
    rw [Complex.ofReal_ratCast]
    change (rationalCone p (N^52) (coneWidth N):ℂ)-_ = windowExtension (above T L) (2*N^52) p
    change (rationalCone p (N^52) (coneWidth N):ℂ)-_ = (model T N p:ℂ) at hs
    linear_combination hs
  have hh' : |(rationalCone p (N^52) (coneWidth N):ℝ)-model T N p|=‖F‖ := by
    rw [←Real.norm_eq_abs,←Complex.norm_real,Complex.ofReal_sub,heq]
  have hs₁ := abs_sub_le ((S p:ℝ)/p-log p/2) (offDiagonal p/p) (c*(rationalCone p (N^52) (coneWidth N):ℝ))
  have hs₂ := abs_sub_le ((S p:ℝ)/p-log p/2) (c*(rationalCone p (N^52) (coneWidth N):ℝ)) (c*model T N p)
  rw [←mul_sub,abs_mul,abs_of_pos hc,hh'] at hs₂
  change |(S p:ℝ)/p-log p/2-c*model T N p|≤C+2265902+c*‖F‖
  change |offDiagonal p/p-c*(rationalCone p (N^52) (coneWidth N):ℝ)|≤_ at he
  linarith only [hdiag,he.trans hb,hs₁,hs₂]

/-- Both contributions are explicit: bounded diagonal error per selected prime,
and a decaying tail cost at the full prime-band scale. -/
theorem square : ∃ D B : ℝ, 0<D ∧ 0≤B ∧ ∀ {N T : ℕ}, 2≤N → 1≤T → T≤N →
    ∀ s : Finset ℕ, (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64) →
    ∑ p∈s,((S p:ℝ)/p-log p/2-(8/Real.pi^2)*model T N p)^2 ≤
      D*s.card+B*(N:ℝ)^64/(log N*(T:ℝ)^(1/128:ℝ)) := by
  obtain ⟨D,hD,hd⟩ := signed
  obtain ⟨B,hB,hb⟩ := ThetaSievedConcentration.high_variance
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨2*D^2,2*c^2*B,by positivity,by positivity,?_⟩
  intro N T hN hT hTN s hs
  let F (p : ℕ) := windowExtension (above T (coneWindow (coneWidth N))) (2*N^52) p
  have hw : 0<log N*(T:ℝ)^(1/128:ℝ) := mul_pos
    (log_pos (by exact_mod_cast (show 1<N by omega))) (rpow_pos_of_pos (by exact_mod_cast (show 0<T by omega)) _)
  have H := (le_div_iff₀ hw).mpr (hb hN hT hTN (coneWindow (coneWidth N)) (by simp [coneWindow]) s hs)
  change (∑ p∈s,‖F p‖^2)≤_ at H
  calc _ ≤ ∑ p∈s,(2*D^2+(2*c^2)*‖F p‖^2) := by
             apply sum_le_sum; intro p hp
             obtain ⟨hpr,hl,hh⟩ := hs p hp
             have h := pow_le_pow_left₀ (abs_nonneg _) (hd hN hTN hpr hl hh) 2
             rw [sq_abs] at h
             change _ ≤ (D+c*‖F p‖)^2 at h
             nlinarith only [h,sq_nonneg (D-c*‖F p‖)]
       _ ≤ _ := by
             rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum (s:=s) (f:=fun p => ‖F p‖^2)]
             calc _ ≤ (s.card:ℝ)*(2*D^2)+(2*c^2)*(B*(N:ℝ)^64/(log N*(T:ℝ)^(1/128:ℝ))) :=
                    add_le_add_right (mul_le_mul_of_nonneg_left H (by positivity)) _
                  _ = _ := by ring

#print axioms square
end
end Arxiv.«2501.03234».ThetaMovingPrimeModelError
