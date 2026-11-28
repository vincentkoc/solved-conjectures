import ThetaUniformExcursions

/-! Transfer the matching lower tail to all sufficiently large prime endpoints. -/
namespace Arxiv.«2501.03234».ThetaUniformExcursionEndpoint
open Finset Filter Real ThetaUniformExcursions
noncomputable section

def primes (X q r : ℕ) (z v : ℝ) :=
  (Nat.primesLE X).filter (fun p => p%q=r ∧ v ≤ z*((S p:ℝ)/p-log p/2))

theorem endpoints (H : ThetaExceptionalPrimeInput.Ordinary) : ∃ η : ℝ,0<η ∧ ∃ X₀ : ℕ,∀ᶠ T : ℕ in atTop,
    ∀ X≥X₀,2147483648*(T:ℝ) ≤ (log (X:ℝ))^(1/3:ℝ) →
    ∀ q r : ℕ,0<q → r<q → r.Coprime q → log q ≤ η*log T →
    ∀ z : ℝ,|z|=1 → (X.primeCounting:ℝ)*exp (-(262144*(T:ℝ))) ≤ ((primes X q r z (height T)).card:ℝ) := by
  obtain ⟨η,hη,N₀,ht⟩ := band_hits H
  have hlog := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp hlog
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hu
  obtain ⟨X₁,hU⟩ := eventually_atTop.mp hu
  refine ⟨η,hη,max ((max 2 (max N₀ N₁))^64) X₁,?_⟩
  filter_upwards [ht,eventually_ge_atTop 1] with T hT hTp X hX hhigh q r hq hr hcop hqt z hz
  let N := Nat.nthRoot 64 X
  have hn : max 2 (max N₀ N₁) ≤ N := (Nat.le_nthRoot_iff (by decide : 64≠0)).mpr ((le_max_left ..).trans hX)
  have hN₂ : 2≤N := (le_max_left ..).trans hn
  have hN₀ := ((le_max_left N₀ N₁).trans (le_max_right ..)).trans hn
  have hN₁ := ((le_max_right N₀ N₁).trans (le_max_right ..)).trans hn
  have hL : 1≤log (N:ℝ) := h₁ N hN₁
  have hp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hlo : N^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhi : X≤2^64*N^64 := calc
    X ≤ (N+1)^64 := (Nat.lt_pow_nthRoot_add_one (by decide) X).le
    _ ≤ (2*N)^64 := Nat.pow_le_pow_left (by omega) _
    _ = _ := Nat.mul_pow ..
  have hh : (X:ℝ) ≤ 2^64*(N:ℝ)^64 := by exact_mod_cast hhi
  have hx : 0<(X:ℝ) := (pow_pos hp 64).trans_le (by exact_mod_cast hlo)
  have hlogX := log_le_log hx hh
  rw [log_mul (by positivity) (by positivity),log_pow,log_pow] at hlogX
  norm_num only [Nat.cast_ofNat] at hlogX
  have h2 := log_le_log (by norm_num : 0<(2:ℝ)) (by exact_mod_cast hN₂ : (2:ℝ)≤N)
  have hL' : log (X:ℝ) ≤ 128*log (N:ℝ) := by linarith only [h2,hlogX]
  have hNL := log_le_log hp (Nat.cast_le.mpr ((Nat.le_self_pow (by decide : 64≠0) N).trans hlo))
  have had : 134217728*(T:ℝ) ≤ (log (N:ℝ))^(1/3:ℝ) := by
    have hX' := rpow_le_rpow (show 0≤log (X:ℝ) by linarith only [hL,hNL]) hL' (by norm_num : (0:ℝ)≤1/3)
    rw [mul_rpow (by norm_num : (0:ℝ)≤128) (by linarith)] at hX'
    have h128 : (128:ℝ)^(1/3:ℝ) ≤ 8 := by
      calc _ ≤ ((8:ℝ)^3)^(1/3:ℝ) := rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
           _ = _ := by rw [←rpow_natCast_mul (by norm_num : (0:ℝ)≤8)];norm_num
    have hR := mul_le_mul_of_nonneg_right h128 (rpow_nonneg (by linarith only [hL] : 0≤log (N:ℝ)) (1/3))
    linarith only [hhigh,hX',hR,Nat.cast_nonneg (α:=ℝ) T]
  have hs : hits N q r z (height T) ⊆ primes X q r z (height T) := by
    intro p h;obtain ⟨hb,rest⟩ := mem_filter.mp h
    obtain ⟨hpr,_,hle⟩ := ThetaSiegelWalfiszBand.mem_band.mp hb
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle.trans hlo,hpr⟩,rest⟩
  have hposL : 0<log (N:ℝ) := by linarith
  have hposX := hposL.trans_le hNL
  have hpi := (le_div_iff₀ hposX).mp (hU X ((le_max_right ..).trans hX))
  have h4 : log (4:ℝ)+1 ≤ 4 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hcomp : (X.primeCounting:ℝ) ≤ 2^66*((N:ℝ)^64/log N) := by
    rw [←mul_div_assoc,le_div_iff₀ hposL]
    calc _ ≤ X.primeCounting*log (X:ℝ) := mul_le_mul_of_nonneg_left hNL (Nat.cast_nonneg _)
         _ ≤ (log 4+1)*X := hpi
         _ ≤ 4*(2^64*(N:ℝ)^64) := mul_le_mul h4 hh hx.le (by norm_num)
         _ = _ := by ring
  have hscale : (2:ℝ)^66*exp (-(262144*(T:ℝ))) ≤ exp (-(131072*(T:ℝ))) := by
    rw [←exp_log (by norm_num : 0<(2:ℝ)),←exp_nat_mul,←exp_add,exp_le_exp]
    norm_num only [Nat.cast_ofNat]
    have ht' : (1:ℝ)≤T := by exact_mod_cast hTp
    linarith only [log_two_lt_d9,ht']
  apply le_trans _ ((hT N hN₀ had q r hq hr hcop hqt z hz).trans (Nat.cast_le.mpr (card_le_card hs)))
  calc _ ≤ (2^66*((N:ℝ)^64/log N))*exp (-(262144*(T:ℝ))) := mul_le_mul_of_nonneg_right hcomp (exp_pos _).le
       _ = ((N:ℝ)^64/log N)*(2^66*exp (-(262144*(T:ℝ)))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hscale (div_nonneg (pow_nonneg hp.le 64) hposL.le)

#print axioms endpoints
end
end Arxiv.«2501.03234».ThetaUniformExcursionEndpoint
