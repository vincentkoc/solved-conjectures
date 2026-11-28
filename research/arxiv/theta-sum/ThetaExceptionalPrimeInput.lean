import ThetaFiberDiscrepancy
import ThetaSiegelWalfiszBand

/-! A theta-free ordinary prime-count input with one possible exceptional conductor. -/
namespace Arxiv.«2501.03234».ThetaExceptionalPrimeInput
open Real Finset Filter ThetaFiberDiscrepancy ThetaSiegelWalfiszBand
noncomputable section

def radius (x : ℝ) := exp ((log x)^(1/3:ℝ))
def center (f q b : ℕ) (main : ℝ) (corr : ℕ → ℝ) := if f∣q then corr (b%f) else main

/-- Log-weighted ordinary primes. The secondary main term depends just on
the residue modulo one conductor, when that conductor divides the modulus. -/
def Ordinary : Prop := ∃ κ : ℝ,0<κ ∧ ∀ᶠ X : ℕ in atTop,∃ f : ℕ,∃ V : ℕ → ℝ,0<f ∧
    (∀ b,κ*X/(f:ℝ)^2 ≤ V b) ∧
    ∀ q b : ℕ,0<q → (q:ℝ) ≤ radius X → b<q → b.Coprime q →
      |mass (Nat.primesLE X) (fun p => log p) q b-center f q b X V/(q.totient:ℝ)| ≤ X/(radius X)^2

def weight (N p : ℕ) := log p/(64*log N)
def error (N : ℕ) := 3*(N:ℝ)^64/radius N
def Data (N f : ℕ) (main : ℝ) (corr : ℕ → ℝ) : Prop := ∀ q b : ℕ,0<q →
    (q:ℝ) ≤ radius N → b<q →
      |mass (band N) (weight N) q b-(if b.Coprime q then center f q b main corr/(q.totient:ℝ) else 0)| ≤ error N

theorem radius_pos (x : ℝ) : 0<radius x := exp_pos _
theorem radius_bounds {x : ℝ} (hx : 1≤log x) (hp : 0<x) : 1≤radius x ∧ radius x≤x := by
  unfold radius
  exact ⟨one_le_exp (rpow_nonneg (by linarith) _),by
    rw [←exp_log hp,exp_le_exp,log_exp];exact rpow_le_self_of_one_le hx (by norm_num)⟩

theorem weights {N p : ℕ} (hN : 2≤N) (hp : p∈band N) : 1/2 ≤ weight N p ∧ weight N p ≤ 1 := by
  obtain ⟨hpr,hlo,hhi⟩ := mem_band.mp hp
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hL := log_pos hn
  have hl := log_le_log (by positivity : 0<(N:ℝ)^56) (by exact_mod_cast hlo : (N:ℝ)^56≤p)
  have hh := log_le_log (by exact_mod_cast hpr.pos : 0<(p:ℝ)) (by exact_mod_cast hhi : (p:ℝ)≤(N:ℝ)^64)
  rw [log_pow] at hl hh;norm_num only [Nat.cast_ofNat] at hl hh
  unfold weight;constructor
  · rw [le_div_iff₀ (by positivity)];linarith only [hl,hL]
  · rw [div_le_one (by positivity)];exact hh

private theorem small {N q b : ℕ} (hN : 2≤N) :
    |mass (band N) (weight N) q b-mass (Nat.primesLE (N^64)) (fun p => log p) q b/(64*log N)| ≤ (N:ℝ)^56 := by
  classical
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hL := log_pos hn
  let A := (Nat.primesLE (N^64)).filter (fun p => p%q=b)
  let D := (band N).filter (fun p => p%q=b)
  have hsub : D⊆A := fun p hp => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
  have hlow : A \ D ⊆ range (N^56) := by
    intro p hp;obtain ⟨ha,hd⟩ := mem_sdiff.mp hp
    apply mem_range.mpr;by_contra! h
    exact hd (mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp ha).1,h⟩,(mem_filter.mp ha).2⟩)
  have he : (∑ p∈A,weight N p)=mass (Nat.primesLE (N^64)) (fun p => log p) q b/(64*log N) := by
    simp only [A,weight,mass,sum_div]
  have hw (p : ℕ) (hp : p∈A \ D) : 0 ≤ weight N p ∧ weight N p ≤ 1 := by
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp (mem_filter.mp (mem_sdiff.mp hp).1).1
    have hh := log_le_log (by exact_mod_cast hpr.pos : 0<(p:ℝ)) (by exact_mod_cast hle : (p:ℝ)≤(N:ℝ)^64)
    rw [log_pow] at hh;norm_num only [Nat.cast_ofNat] at hh
    exact ⟨div_nonneg (ThetaDivisorLogMean.log_nonneg_nat _) (by positivity),(div_le_one (by positivity : 0<64*log (N:ℝ))).mpr hh⟩
  have hz := sum_nonneg (s:=A \ D) (fun p hp => (hw p hp).1)
  have hc : (∑ p∈A \ D,weight N p) ≤ (N:ℝ)^56 := calc
    _ ≤ ∑ _p∈A \ D,(1:ℝ) := sum_le_sum (fun p hp => (hw p hp).2)
    _ = ((A \ D).card:ℝ) := by simp
    _ ≤ _ := by exact_mod_cast (card_le_card hlow).trans_eq (card_range _)
  have hh := sum_sdiff hsub (f:=weight N)
  rw [←he];change |(∑ p∈D,weight N p)-∑ p∈A,weight N p|≤_
  rw [←hh,show (∑ p∈D,weight N p)-((∑ p∈A \ D,weight N p)+∑ p∈D,weight N p) = -(∑ p∈A \ D,weight N p) by ring,abs_neg,abs_of_nonneg hz]
  exact hc

theorem band_input (H : Ordinary) : ∃ κ : ℝ,0<κ ∧ ∀ᶠ N : ℕ in atTop,∃ f : ℕ,∃ (main : ℝ) (V : ℕ → ℝ),
    0<f ∧ κ*(N:ℝ)^64/log N ≤ main ∧ (∀ b,κ*(N:ℝ)^64/(log N*(f:ℝ)^2) ≤ V b) ∧ Data N f main V := by
  obtain ⟨κ,hκ,ho⟩ := H
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨min 1 κ/64,by positivity,?_⟩
  filter_upwards [(tendsto_pow_atTop (n:=64) (by decide)).eventually ho,hlog.eventually_ge_atTop 1,eventually_ge_atTop 2] with N hN hL h₂
  obtain ⟨f,V,hf,hV,hq⟩ := hN
  change 1≤log (N:ℝ) at hL
  have hl : 0<log (N:ℝ) := by linarith
  have hn : (1:ℝ)<N := by exact_mod_cast h₂
  have hp := lt_trans zero_lt_one hn
  let X := N^64
  let B := 64*log (N:ℝ)
  have hB : 1≤B := by dsimp [B];linarith
  have hB' : 0<B := by linarith
  have hx : (X:ℝ)=(N:ℝ)^64 := Nat.cast_pow ..
  have hR := radius_bounds hL hp
  have hRX : radius N ≤ radius X := by
    unfold radius;apply exp_le_exp.mpr;apply rpow_le_rpow hl.le _ (by norm_num)
    rw [hx,log_pow];norm_num;linarith
  refine ⟨f,(X:ℝ)/B,fun b => V b/B,hf,?_,?_,?_⟩
  · rw [hx];dsimp [B];field_simp
    exact min_le_left ..
  · intro b
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) κ) (pow_nonneg hp.le 64)
    have hb := hV b;rw [hx] at hb
    dsimp [B];have hfr : 0<(f:ℝ) := Nat.cast_pos.mpr hf
    rw [div_le_iff₀ (sq_pos_of_pos hfr)] at hb
    field_simp; nlinarith only [hb,hh]
  intro q b hqp hqr hb
  have hqN : q≤N := by exact_mod_cast hqr.trans hR.2
  by_cases hcop : b.Coprime q
  · rw [if_pos hcop]
    have hh := hq q b hqp (hqr.trans hRX) hb hcop
    have hp₁ := small (q:=q) (b:=b) h₂
    have hd : |mass (Nat.primesLE X) (fun p => log p) q b/B-
        center f q b ((X:ℝ)/B) (fun a => V a/B)/(q.totient:ℝ)| ≤ ((X:ℝ)/(radius X)^2)/B := by
      have he : center f q b ((X:ℝ)/B) (fun a => V a/B)/(q.totient:ℝ) =
          center f q b X V/(q.totient:ℝ)/B := by unfold center;split_ifs <;> ring
      rw [he,←sub_div,abs_div,abs_of_pos hB'];exact div_le_div_of_nonneg_right hh hB'.le
    have hsc : (N:ℝ)^56 ≤ (N:ℝ)^64/radius N := by
      rw [le_div_iff₀ (radius_pos _)];apply (mul_le_mul_of_nonneg_left hR.2 (by positivity : 0 ≤ (N:ℝ)^56)).trans
      rw [←pow_succ];exact pow_le_pow_right₀ hn.le (by decide)
    have herr : ((X:ℝ)/(radius X)^2)/B ≤ (N:ℝ)^64/radius N := by
      calc _ ≤ (X:ℝ)/(radius X)^2 := div_le_self (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hB
           _ ≤ (X:ℝ)/radius N := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (radius_pos _) (hRX.trans (le_self_pow₀ (hR.1.trans hRX) (by decide : 2≠0)))
           _ = _ := by rw [hx]
    have h := abs_sub_le (mass (band N) (weight N) q b) (mass (Nat.primesLE X) (fun p => log p) q b/B)
      (center f q b ((X:ℝ)/B) (fun a => V a/B)/(q.totient:ℝ))
    apply h.trans ((add_le_add hp₁ hd).trans ((add_le_add hsc herr).trans ?_))
    unfold error;rw [mul_div_assoc]
    have hpos := div_nonneg (pow_nonneg hp.le 64) (radius_pos (N:ℝ)).le
    linarith only [hpos]
  · rw [if_neg hcop];have hz : (band N).filter (fun p => p%q=b)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr;intro p h
      obtain ⟨ha,hr⟩ := mem_filter.mp h;obtain ⟨hpr,hlo,_⟩ := mem_band.mp ha
      have hnp : N<p := (show N<N^56 by simpa only [pow_one] using Nat.pow_lt_pow_right (by omega : 1<N) (show 1<56 by decide)).trans_le hlo
      have hc := hpr.coprime_iff_not_dvd.mpr (fun hh => (lt_of_le_of_lt hqN hnp).not_ge (Nat.le_of_dvd hqp hh))
      exact hcop (by rw [←hr,←ZMod.isUnit_iff_coprime,ZMod.natCast_mod,ZMod.isUnit_iff_coprime];exact hc)
    simp only [mass,hz,sum_empty,sub_zero,abs_zero,error]
    exact div_nonneg (by positivity) (radius_pos _).le

#print axioms band_input
end
end Arxiv.«2501.03234».ThetaExceptionalPrimeInput
