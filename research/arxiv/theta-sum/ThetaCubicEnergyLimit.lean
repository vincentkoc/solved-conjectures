import ThetaCubicEnergy

/-! Every large prime has asymptotically half of its cubic energy in the real part. -/

namespace Arxiv.«2501.03234».ThetaCubicEnergyLimit
open Filter Finset Real DirichletCharacter ThetaPointwiseCutoff ThetaCubicEnergy
open Asymptotics
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem relative_error (hp : p%2=1) :
    |realEnergy (nonprincipal p)/total (nonprincipal p)-1/2| ≤
        1536*(harmonic (p/2):ℝ)^6/(p:ℝ)^(1/4:ℝ) := by
  have hprime : p.Prime := Fact.out
  have hx : 1≤(p:ℝ) := by exact_mod_cast hprime.one_le
  have hx₀ : 0<(p:ℝ) := by linarith
  have hφ : (0:ℝ)<p.totient := by exact_mod_cast Nat.totient_pos.mpr hprime.pos
  have hlarge : (p:ℝ)≤2*(p.totient:ℝ) := by
    rw [Nat.totient_prime hprime]
    exact_mod_cast (show p≤2*(p-1) by have := hprime.two_le; omega)
  have hsmall : (p.totient:ℝ)≤p := by exact_mod_cast Nat.totient_le p
  have hquart : 0<(p:ℝ)^(1/4:ℝ) := by positivity
  have hthree := one_le_rpow hx (by norm_num : (0:ℝ)≤3/4)
  have hprod : (p:ℝ)^(3/4:ℝ)*(p:ℝ)^(1/4:ℝ)=p := by rw [←rpow_add hx₀]; norm_num
  have ht : (p.totient:ℝ)*(2*(p:ℝ)^(3/4:ℝ))+1 ≤ 3*(p:ℝ)*(p:ℝ)^(3/4:ℝ) := by
    have h1 := one_le_mul_of_one_le_of_one_le hx hthree
    nlinarith only [h1,mul_le_mul_of_nonneg_right hsmall (show 0≤(p:ℝ)^(3/4:ℝ) by positivity)]
  have hfour := pow_le_pow_left₀ hx₀.le hlarge 4
  have hh : (0:ℝ)≤(harmonic (p/2):ℝ)^6 := by positivity
  apply (fraction_error hp).trans
  apply (div_le_div_iff₀ (by positivity) hquart).mpr
  calc
    _ ≤ 32*((p:ℝ)^2*(3*p*(p:ℝ)^(3/4:ℝ))*(harmonic (p/2):ℝ)^6)*(p:ℝ)^(1/4:ℝ) := by gcongr
    _ = 96*(p:ℝ)^4*(harmonic (p/2):ℝ)^6 := by
      linear_combination 96*(p:ℝ)^3*(harmonic (p/2):ℝ)^6*hprod
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hfour hh]

theorem half_fraction {η : ℝ} (hη : 0<η) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      |realEnergy (nonprincipal p)/total (nonprincipal p)-1/2| < η := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hl := ((isLittleO_log_rpow_rpow_atTop 6 (by norm_num : (0:ℝ)<1/4)).natCast_atTop).bound
    (show (0:ℝ)<η/200000 by positivity)
  filter_upwards [hl,ht.eventually_ge_atTop 1] with p h hlp
  intro hprime hp
  let : Fact p.Prime := ⟨hprime⟩
  have hpos : 0<p/2 := Nat.div_pos hprime.two_le (by decide)
  have hh : (harmonic (p/2):ℝ)≤2*log p := by
    have hle := log_le_log (show 0<((p/2:ℕ):ℝ) by exact_mod_cast hpos)
      (by exact_mod_cast (Nat.div_le_self p 2) : ((p/2:ℕ):ℝ)≤p)
    change 1≤log (p:ℝ) at hlp
    linarith [harmonic_le_one_add_log (p/2)]
  have hhar : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (harmonic_pos hpos.ne').le
  have hpow := pow_le_pow_left₀ hhar hh 6
  have hx : (0:ℝ)<(p:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hprime.pos) _
  change ‖(log (p:ℝ))^(6:ℝ)‖≤_*‖(p:ℝ)^(1/4:ℝ)‖ at h
  rw [show (6:ℝ)=(6:ℕ) by norm_num,Real.rpow_natCast,Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg hx.le] at h
  apply (relative_error (Nat.odd_iff.mp hp)).trans_lt
  apply (div_lt_iff₀ hx).mpr
  nlinarith only [hpow,h,mul_pos hη hx]

#print axioms relative_error
#print axioms half_fraction
end
end Arxiv.«2501.03234».ThetaCubicEnergyLimit
