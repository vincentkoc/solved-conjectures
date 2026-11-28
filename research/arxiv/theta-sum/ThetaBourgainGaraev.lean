import ThetaShortSumTransfer

/-! The classical Bourgain–Garaev initial reciprocal-sum bound implies a uniform
logarithmic saving for the canonical integer theta sum. -/

namespace Arxiv.«2501.03234».ThetaBourgainGaraev
open Real Filter ThetaReciprocalPrefixes ThetaShortSumTransfer

/-- The only external estimate in the transfer. The reciprocal sum runs over
the integers from one through N, inclusive. -/
def InitialSumEstimate : Prop := ∃ c : ℝ, 1≤c ∧ ∀ᶠ p : ℕ in atTop,
  ∀ [Fact p.Prime], PrefixBound p (c*log p*(log (log p))^3)

theorem original_bound (estimate : InitialSumEstimate) :
    ∃ A : ℝ, 0<A ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      |(S p : ℝ)| ≤ A*p*log p*sqrt (log p)*(log (log p))^4 := by
  obtain ⟨c,hc,hest⟩ := estimate
  obtain ⟨C,hC,htransfer⟩ := original_transfer
  refine ⟨C+37+40960*c,by linarith,?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hloglog := tendsto_log_atTop.comp hlog
  filter_upwards [hest,hlog.eventually_ge_atTop 1,hloglog.eventually_ge_atTop 1,
    eventually_ge_atTop 4] with p he hu hv hp₄
  intro hp
  have : Fact p.Prime := ⟨hp⟩
  let u := log (p:ℝ)
  let v := log u
  let t := Nat.log 2 p
  let z := u*sqrt u*v^4
  change 1≤u at hu
  change 1≤v at hv
  have hu₀ : 0<u := by linarith
  have hv₀ : 0<v := by linarith
  have ht : 2≤t := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : p≠0)).2 hp₄
  have htv : 0<(t:ℝ) := by exact_mod_cast (show 0<t by omega)
  have hpower := Nat.pow_log_le_self 2 (by omega : p≠0)
  have hlogt := log_le_log (show 0<(2:ℝ)^t by positivity) (show (2:ℝ)^t≤p by exact_mod_cast hpower)
  rw [log_pow] at hlogt
  have htu : (t:ℝ)≤2*u := by
    have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)/2≤log 2 by linarith [log_two_gt_d9]) htv.le
    change (t:ℝ)*log 2≤u at hlogt
    linarith
  have hht : (harmonic t:ℝ)+2≤5*v := by
    have h := log_le_log htv htu
    rw [log_mul (by norm_num) hu₀.ne'] at h
    change log (t:ℝ) ≤ log 2+v at h
    linarith [harmonic_le_one_add_log t, log_two_lt_d9]
  have hhhalf : (harmonic (p/2):ℝ)≤1+u := by
    apply (harmonic_le_one_add_log _).trans
    apply add_le_add_right
    exact log_le_log (by exact_mod_cast (show 0<p/2 by omega)) (by exact_mod_cast (show p/2≤p by omega))
  have hsqrt : sqrt (t:ℝ)≤2*sqrt u := by
    have h := sqrt_le_sqrt (htu.trans (by linarith : 2*u≤4*u))
    simpa [sqrt_mul (by norm_num : (0:ℝ)≤4), show sqrt (4:ℝ)=2 by norm_num] using h
  have hz : u≤z := by
    dsimp [z]
    calc
      _ = u*1*1 := by ring
      _ ≤ _ := by
        gcongr
        · simpa using sqrt_le_sqrt hu
        · exact one_le_pow₀ hv
  have hz₁ : 1≤z := hu.trans hz
  have hK : 1 ≤ c*u*v^3 := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hc hu) (one_le_pow₀ hv)
  have hhh : 0≤(harmonic t:ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; positivity
  have hlarge : ((harmonic t:ℝ)+2)*(c*u*v^3)*sqrt t ≤ 10*c*z := by
    calc
      _ ≤ (5*v)*(c*u*v^3)*(2*sqrt u) := by gcongr
      _ = _ := by dsimp [z]; ring
  have h := htransfer p (Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))) hp₄ _ hK he
  calc
    _ ≤ (p:ℝ)*(C+2*harmonic (p/2)+u/2+16*t+4096*(((harmonic t:ℝ)+2)*(c*u*v^3)*sqrt t)) := by
      apply h.trans_eq
      dsimp only [u,v,t]
      ring
    _ ≤ (p:ℝ)*((C+37+40960*c)*z) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hCz := mul_le_mul_of_nonneg_left hz₁ hC.le
      nlinarith only [hCz,hz,hz₁,hlarge,htu,hhhalf]
    _ = _ := by dsimp [z,u,v]; ring

open Asymptotics in
theorem log_power_saving (estimate : InitialSumEstimate) {ε : ℝ} (hε : 0<ε) :
    (fun p : ℕ => (S p : ℝ)) =o[atTop ⊓ principal {p : ℕ | p.Prime}]
      (fun p : ℕ => (p:ℝ)*(log p)^((3:ℝ)/2+ε)) := by
  let l := (atTop : Filter ℕ) ⊓ principal {p : ℕ | p.Prime}
  have hl : l ≤ atTop := inf_le_left
  have ht := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).mono_left hl
  obtain ⟨A,hA,H⟩ := original_bound estimate
  have hmain : (fun p : ℕ => (S p : ℝ)) =O[l]
      (fun p : ℕ => ((p:ℝ)*log p*sqrt (log p))*(log (log p))^4) := by
    apply IsBigO.of_bound A
    rw [eventually_inf_principal]
    filter_upwards [H,eventually_ge_atTop (1:ℕ)] with p h hp hpr
    have hlog : 0≤log (p:ℝ) := log_nonneg (by exact_mod_cast hp)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0≤((p:ℝ)*log p*sqrt (log p))*(log (log p))^4 by positivity)]
    calc
      _ ≤ _ := h hpr
      _ = _ := by ring
  have hsmall : (fun p : ℕ => (log (log p))^4) =o[l] (fun p : ℕ => (log p)^ε) := by
    have hh := (isLittleO_log_rpow_rpow_atTop 4 hε).comp_tendsto ht
    simpa only [Function.comp_def, show (4:ℝ)=(4:ℕ) by norm_num, Real.rpow_natCast] using hh
  apply hmain.trans_isLittleO
  have h := (isBigO_refl (fun p : ℕ => (p:ℝ)*log p*sqrt (log p)) l).mul_isLittleO hsmall
  apply h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [ht.eventually_gt_atTop 0] with p hp
  change (p:ℝ)*log p*sqrt (log p)*(log p)^ε = (p:ℝ)*(log p)^((3:ℝ)/2+ε)
  change 0 < log (p:ℝ) at hp
  rw [rpow_add hp, show (3:ℝ)/2=1+(1:ℝ)/2 by norm_num, rpow_add hp, rpow_one,
    ← sqrt_eq_rpow]
  ring

#print axioms original_bound
#print axioms log_power_saving
end Arxiv.«2501.03234».ThetaBourgainGaraev
