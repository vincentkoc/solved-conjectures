import ThetaPrimeRuns

/-! Long consecutive runs in the increasing list of primes in each reduced progression. -/
namespace Arxiv.«2501.03234».ThetaShortPrimeRuns
open Finset Filter Real ThetaPrimeRuns ThetaShortProgressions ThetaBackwardInterval
open ThetaStrongOriginalTail ThetaStrongDeviation ThetaWeilShortIntervals ThetaShortPrimeInterval
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable _

def depth (x : ℕ) := exp (rate (left x)/8192)

theorem depth_tendsto : Tendsto depth atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have h := tendsto_left.eventually (absorb_log_power (by positivity : 0 < |b|+1)
    (by norm_num : (0:ℝ)<8192) 0)
  filter_upwards [h] with x hx
  simp only [pow_zero,mul_one] at hx
  exact (by linarith only [le_abs_self b] : b ≤ |b|+1).trans hx

theorem many (A : Finset ℕ) (bad : ℕ → Prop) {F W : ℝ} (hF : 1≤F)
    (hW : F^3≤W) (hA : W≤(A.card:ℝ)*F)
    (hE : ((A.filter bad).card:ℝ)≤2*W/F^4) :
    (1-3/F)*A.card≤((starts A ⌊F⌋₊ bad).card:ℝ) := by
  let L := ⌊F⌋₊
  let P := (A.card:ℝ)
  let E := ((A.filter bad).card:ℝ)
  let G := ((starts A L bad).card:ℝ)
  have hf : 0<F := by linarith
  have hL : (L:ℝ)≤F := Nat.floor_le hf.le
  have hh : P≤G+(L:ℝ)*E+L := by dsimp only [P,G,E]; exact_mod_cast deletion A L bad
  have hP : F^2≤P := by
    apply (mul_le_mul_iff_left₀ hf).mp
    nlinarith only [hW.trans hA]
  have hE' : E*F^3≤2*P := by
    apply (mul_le_mul_iff_left₀ hf).mp
    have h := (le_div_iff₀ (pow_pos hf 4)).mp hE
    change E*F^4≤2*W at h
    change W≤P*F at hA
    nlinarith only [h,hA]
  have he : 0≤E := Nat.cast_nonneg _
  have hsmall : (L:ℝ)*E*F≤2*P := by
    apply le_trans _ hE'
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL he) hf.le
    have h' := mul_le_mul_of_nonneg_left hF (mul_nonneg he (sq_nonneg F))
    nlinarith only [h,h']
  have hend : (L:ℝ)*F≤P := (mul_le_mul_of_nonneg_right hL hf.le).trans (by nlinarith only [hP])
  change (1-3/F)*P≤G
  apply (mul_le_mul_iff_left₀ hf).mp
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hh hf.le,hsmall,hend]

/-- Rank deletion in a reduced progression from ordinary prime counts, a
global count of deviations in this window, and a proposed run length. -/
theorem of_count {x K : ℕ} {ε F : ℝ}
    (hc : ∀ q a : ℕ, 0<q → (q:ℝ)≤(log x)^K → a.Coprime q →
      (1/250:ℝ)*width x/((q.totient:ℝ)*log x)≤((window x (fun p => p ≡ a [MOD q])).card:ℝ))
    (hlog : 0<log (x:ℝ)) (hF : 1≤F) (hW : F^3≤width x)
    (hfac : 250*(log (x:ℝ))^(K+1)≤F)
    (hexc : ((window x (deviates ε)).card:ℝ)≤2*width x/F^4) :
    ∀ q a : ℕ, 0<q → (q:ℝ)≤(log x)^K → a.Coprime q →
      let A := window x (fun p => p ≡ a [MOD q])
      (1-3/F)*A.card ≤ ((starts A ⌊F⌋₊ (deviates ε)).card:ℝ) := by
  intro q a hq hsize hcop
  let A := window x (fun p => p ≡ a [MOD q])
  have hφ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hφq : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  have hfac' : 250*((q.totient:ℝ)*log x)≤F := by
    have h := mul_le_mul_of_nonneg_right (hφq.trans hsize) hlog.le
    rw [←pow_succ] at h
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤250)).trans hfac
  have hA : width x≤(A.card:ℝ)*F := by
    have hh := (div_le_iff₀ (mul_pos hφ hlog)).mp (hc q a hq hsize hcop)
    change (1/250:ℝ)*width x≤(A.card:ℝ)*_ at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hfac' (Nat.cast_nonneg A.card)]
  apply many A (deviates ε) hF hW hA
  have hsub : A.filter (deviates ε) ⊆ window x (deviates ε) := by
    intro p hp
    obtain ⟨hm,hd⟩ := mem_filter.mp hp
    obtain ⟨hi,hp,_⟩ := mem_primes.mp hm
    exact mem_primes.mpr ⟨hi,hp,hd⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hexc

/-- All but at most the fraction 3/depth(x) of the primes in each eligible progression
start a run of floor(depth(x)) consecutive primes of the same progression, all of which
lie in the given backward interval and obey the two-sided theta estimate. -/
theorem runs (weil : Weil) {K : ℕ} (li : Ordinary K) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ x : ℕ in atTop, ∀ q a : ℕ, 0<q → (q:ℝ)≤(log x)^K → a.Coprime q →
    let A := window x (fun p => p ≡ a [MOD q])
    (1-3/depth x)*A.card ≤ ((starts A ⌊depth x⌋₊ (deviates ε)).card:ℝ) := by
  let b : ℝ := 250*2^(K+1)
  have hb : 0<b := by dsimp [b];positivity
  have habs := tendsto_left.eventually (absorb_log_power hb (by norm_num : (0:ℝ)<8192) (K+1))
  have exc := tendsto_left.eventually (original_of_bound (square_root weil) he)
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [li,admissible,habs,exc,hlog.eventually_ge_atTop 1] with x hc hx ha hxE hl
  obtain ⟨hwide,hlen,hhi,hl2,hl1⟩ := hx
  let F := depth x
  change 1≤log (x:ℝ) at hl
  have hlog' : 0<log (x:ℝ) := by linarith
  have hxpos : 0<(x:ℝ) := (log_pos_iff (Nat.cast_nonneg x)).mp hlog' |> zero_lt_one.trans
  have hbase : left x≤x := Nat.floor_le_of_le (by linarith only [show 0≤width x by unfold width;positivity])
  have hleft : 0<(left x:ℝ) := by
    by_contra! h; have hz := le_antisymm h (Nat.cast_nonneg _);rw [hz,log_zero] at hl1;linarith
  have hlogs := log_le_log hleft (show (left x:ℝ)≤x by exact_mod_cast hbase)
  have hF : 1≤F := one_le_exp (by unfold rate; positivity)
  have hFpos : 0<F := by linarith
  have hW : F^3≤width x := by
    dsimp [F,depth,width]
    rw [←exp_nat_mul,rpow_def_of_pos hxpos]
    apply exp_le_exp.mpr
    norm_num
    linarith only [rate_le hl1,hlogs,hl]
  have hfac : 250*(log (x:ℝ))^(K+1)≤F := by
    have hh : (log (x:ℝ))^(K+1)≤2^(K+1)*(1+log (left x))^(K+1) := by
      rw [←mul_pow];exact pow_le_pow_left₀ hlog'.le (by linarith only [hl2]) _
    change b*(1+log (left x))^(K+1)≤F at ha
    dsimp [b] at ha
    linarith only [mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤250),ha]
  apply of_count hc hlog' hF hW hfac
  have h := hxE (length x) (by simpa only [←sqrt_eq_rpow] using hwide) hlen
  change ((window x (deviates ε)).card:ℝ)≤(length x:ℝ)/log (left x)*exp (-rate (left x)/2048) at h
  have hid : exp (-rate (left x)/2048)=(F^4)⁻¹ := by
    dsimp [F,depth]
    rw [←exp_nat_mul,←exp_neg]
    congr 1
    norm_num
    ring
  rw [hid] at h
  rw [div_eq_mul_inv]
  exact h.trans (mul_le_mul_of_nonneg_right ((div_le_self (by positivity) hl1).trans hhi) (by positivity))

#print axioms depth_tendsto
#print axioms runs
end
end Arxiv.«2501.03234».ThetaShortPrimeRuns
