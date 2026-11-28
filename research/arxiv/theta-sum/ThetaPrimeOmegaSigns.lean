import ThetaSquareLogPrimeExcursions

/-! Pointwise positive and negative omega results along every fixed reduced progression. -/
namespace Arxiv.«2501.03234».ThetaPrimeOmegaSigns
open Finset Filter Real ThetaUniformExcursionEndpoint ThetaSquareLogPrimeExcursions
noncomputable section

/-- Along each fixed reduced progression, both signed deviations separately
exceed the displayed multiple of the prime's own squared iterated logarithm. -/
theorem frequently (H : ThetaExceptionalPrimeInput.Ordinary) {a : ℝ} (ha : 0<a) (ha' : a<1/3)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hcop : r.Coprime q) {z : ℝ} (hz : |z|=1) :
    ∃ᶠ p : ℕ in atTop,p.Prime ∧ p%q=r ∧ (a*log (log p))^2/(64*π^2) ≤ z*((S p:ℝ)/p-log p/2) := by
  obtain ⟨η,hη,h⟩ := original H
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hll := tendsto_log_atTop.comp hl
  have h₀ := hll.const_mul_atTop ha
  have h₁ := ((tendsto_pow_atTop (n:=2) (by decide)).comp h₀).atTop_div_const (by positivity : (0:ℝ)<64*π^2)
  rw [frequently_atTop]
  intro B
  let b := max B 4
  let M := ∑ p∈range b,|(S p:ℝ)/p-log p/2|
  have hm (p : ℕ) (hp : p<b) : z*((S p:ℝ)/p-log p/2) ≤ M := by
    calc _ ≤ |z*((S p:ℝ)/p-log p/2)| := le_abs_self _
         _ = |(S p:ℝ)/p-log p/2| := by rw [abs_mul,hz,one_mul]
         _ ≤ _ := single_le_sum (fun i _ => abs_nonneg ((S i:ℝ)/i-log i/2)) (mem_range.mpr hp)
  obtain ⟨X,⟨⟨hX,hmod⟩,he⟩,h₂⟩ := ((h a ha ha').and ((h₀.const_mul_atTop hη).eventually_ge_atTop (log (q:ℝ)))).and
    (h₁.eventually_gt_atTop M) |>.and (eventually_ge_atTop 2) |>.exists
  have hπ : 0<(X.primeCounting:ℝ) := by
    rw [←Nat.primesLE_card_eq_primeCounting];exact_mod_cast card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨h₂,Nat.prime_two⟩⟩
  have hcount := hX q r hq hr hcop hmod z hz
  have hh := (mul_pos hπ (exp_pos _)).trans_le hcount
  obtain ⟨p,hp⟩ := card_pos.mp (Nat.cast_pos.mp hh)
  obtain ⟨hp₁,hpr,hheight⟩ := mem_filter.mp hp
  obtain ⟨hle,hPrime⟩ := Nat.mem_primesLE.mp hp₁
  have hbig : b≤p := by
    by_contra! hs
    exact (not_lt_of_ge (hheight.trans (hm p hs))) he
  have h4 : (4:ℝ)≤p := by exact_mod_cast ((le_max_right B 4).trans hbig)
  have hlog : 1≤log (p:ℝ) := by
    have htwo : (1:ℝ)/2 ≤ log 2 := by have h := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2);norm_num at h;linarith
    have hfour : log (4:ℝ)=2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,log_pow];norm_num
    linarith only [log_le_log (by norm_num : (0:ℝ)<4) h4,htwo,hfour]
  have h₃ := log_le_log (by linarith : 0<log (p:ℝ)) (log_le_log (by positivity [hPrime.pos] : 0<(p:ℝ)) (Nat.cast_le.mpr hle))
  refine ⟨p,(le_max_left ..).trans hbig,hPrime,hpr,le_trans ?_ hheight⟩
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg ha.le (log_nonneg hlog))
    (mul_le_mul_of_nonneg_left h₃ ha.le) 2) (by positivity)

#print axioms frequently
end
end Arxiv.«2501.03234».ThetaPrimeOmegaSigns
