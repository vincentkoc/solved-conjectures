import ThetaLocalPrimeCounts

/-! Spectral cutoffs in a translated interval. The upper bound for the low
model is polylogarithmic in log X. -/
namespace Arxiv.«2501.03234».ThetaLocalExcursionScales
open Real Filter ThetaLocalPrimeCounts ThetaIdentityModels
noncomputable section

def cutoff (X : ℕ) := ⌊log (X:ℝ)⌋₊^1024
def height (X : ℕ) := 3*Z*(1+log (cutoff X))^2

theorem logs {a C : ℝ} (ha : 0<a) (hC : 0<C) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, C*(log x)^k≤x^a := by
  have h := (isLittleO_log_rpow_rpow_atTop (k:ℝ) ha).bound (one_div_pos.mpr hC)
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx h1
  have hl := log_nonneg h1
  simp only [rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hl _),abs_of_nonneg (rpow_nonneg (by linarith only [h1] : 0≤x) a)] at hx
  calc _ ≤ C*(1/C*x^a) := mul_le_mul_of_nonneg_left hx hC.le
       _ = _ := by field_simp

theorem cutoff_bounds : ∀ᶠ X : ℕ in atTop, let L := log (X:ℝ)
    2≤cutoff X ∧ L≤(cutoff X:ℝ) ∧ (cutoff X:ℝ)≤L^1024 ∧ (cutoff X:ℝ)≤(X:ℝ)^(1/64:ℝ) ∧
    L^16≤(2:ℝ)^16*(cutoff X:ℝ)^(1/64:ℝ) := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop 4,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (logs (by norm_num : (0:ℝ)<1/64) (by norm_num : (0:ℝ)<1) 1024)] with X hL hpoly
  let L := log (X:ℝ)
  let k := ⌊L⌋₊
  change 4≤L at hL
  have hl : (k:ℝ)≤L := Nat.floor_le (by linarith)
  have hu : L<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk : (2:ℝ)≤k := by linarith only [hL,hu]
  have hk' : 2≤k := by exact_mod_cast hk
  have hcut : (cutoff X:ℝ)=(k:ℝ)^1024 := by simp [cutoff,k,L]
  have hk2 : L≤(k:ℝ)^2 := by nlinarith only [hk,hu,mul_nonneg (show 0≤(k:ℝ)-2 by linarith) (Nat.cast_nonneg k : 0≤(k:ℝ))]
  have hyy := pow_le_pow_left₀ (Nat.cast_nonneg k : 0≤(k:ℝ)) hl 1024
  have hi : 2≤cutoff X := hk'.trans (Nat.le_self_pow (by decide : (1024:ℕ)≠0) k)
  have hx : L≤(k:ℝ)^1024 := hk2.trans (pow_le_pow_right₀ (by linarith only [hk]) (by decide : 2≤1024))
  refine ⟨hi,by rw [hcut]; exact hx,by rw [hcut]; exact hyy,?_,?_⟩
  · rw [hcut]; exact hyy.trans (by simpa using hpoly)
  · rw [hcut,←rpow_natCast_mul (Nat.cast_nonneg k),show ((1024:ℕ):ℝ)*(1/64:ℝ)=16 by norm_num,show (16:ℝ)=((16:ℕ):ℝ) by norm_num,rpow_natCast,←mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith only [hu,hk]) 16

theorem height_small {a : ℝ} (ha : 0<a) : ∀ᶠ X : ℕ in atTop, height X≤(log X)^a := by
  have hZ : 1≤Z := (weight_one (by decide : 0<1) (le_refl 1)).trans (ThetaReciprocalBlocks.commonWeight_bounds 1 1).2
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [cutoff_bounds,(tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    ht.eventually (logs ha (show 0<3*Z*1025^2 by positivity) 2)] with X hY h1 hc
  let L := log (X:ℝ)
  obtain ⟨hy,_,hb,_⟩ := hY
  have hl := log_le_log (show 0<(cutoff X:ℝ) by exact_mod_cast (show 0<cutoff X by omega)) hb
  rw [log_pow] at hl
  change 1≤log L at h1
  have h₀ := log_nonneg (show (1:ℝ)≤cutoff X by exact_mod_cast (show 1≤cutoff X by omega))
  have h₂ := pow_le_pow_left₀ (show 0≤1+log (cutoff X) by linarith) (show 1+log (cutoff X)≤1025*log L by norm_num at hl; linarith only [h1,hl]) 2
  change 3*Z*(1+log (cutoff X))^2≤_
  change 3*Z*1025^2*(log L)^2≤L^a at hc
  apply le_trans _ hc
  nlinarith only [mul_le_mul_of_nonneg_left h₂ (show 0≤3*Z by positivity)]

theorem band {e : ℕ} {θ : ℝ} (hθ : (e:ℝ)/64<θ) : ∀ᶠ X : ℕ in atTop,
    ∃ N : ℕ, 2≤N ∧ N^56≤X ∧ 2*X≤N^64 ∧ cutoff X≤N ∧ log N≤log X ∧
      (N:ℝ)^e*(log X)^16≤(X:ℝ)^θ := by
  let r : ℝ := (e:ℝ)/64
  let C := ((2:ℝ)^65)^r
  have hC : 0<C := by dsimp [C]; positivity
  filter_upwards [cutoff_bounds,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (logs (sub_pos.mpr hθ) hC 16),
      eventually_ge_atTop ((256:ℕ)^64)] with X hcut htail hX
  have hXp : 0<X := (show 0<(256:ℕ)^64 by positivity).trans_le hX
  have hx : 0<(X:ℝ) := by exact_mod_cast hXp
  obtain ⟨N,hN,hl,hu,hcap⟩ := ThetaPrimeConcentration.dyadic_cover (X:=2*X) (by omega)
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hx64 : (X:ℝ)≤(N:ℝ)^64 := by exact_mod_cast (show X≤N^64 by omega)
  have hNX : N^56≤X := by omega
  have hNX' := (Nat.le_self_pow (by decide : 56≠0) N).trans hNX
  have h64 : (N:ℝ)^64≤2^65*(X:ℝ) := by exact_mod_cast hcap.trans_eq (by ring : 2^64*(2*X)=2^65*X)
  have he : (N:ℝ)^e≤C*(X:ℝ)^r := calc
    _ = ((N:ℝ)^64)^r := by rw [←rpow_natCast_mul hNp.le,show ((64:ℕ):ℝ)*r=e by dsimp [r]; ring,rpow_natCast]
    _ ≤ ((2:ℝ)^65*(X:ℝ))^r := rpow_le_rpow (by positivity) h64 (by dsimp [r]; positivity)
    _ = _ := mul_rpow (by positivity) hx.le
  have hL := log_nonneg (show (1:ℝ)≤X by exact_mod_cast hXp)
  refine ⟨N,hN,hNX,hu,?_,log_le_log hNp (by exact_mod_cast hNX'),?_⟩
  · have h := rpow_le_rpow hx.le hx64 (by norm_num : (0:ℝ)≤1/64)
    rw [←rpow_natCast_mul hNp.le,show ((64:ℕ):ℝ)*(1/64:ℝ)=1 by norm_num,rpow_one] at h
    exact_mod_cast hcut.2.2.2.1.trans h
  · calc _ ≤ (C*(X:ℝ)^r)*(log X)^16 := mul_le_mul_of_nonneg_right he (pow_nonneg hL _)
         _ = (X:ℝ)^r*(C*(log X)^16) := by ring
         _ ≤ (X:ℝ)^r*(X:ℝ)^(θ-r) := mul_le_mul_of_nonneg_left htail (rpow_nonneg hx.le _)
         _ = _ := by rw [←rpow_add hx]; congr 1; ring

#print axioms cutoff_bounds
#print axioms height_small
#print axioms band
end
end Arxiv.«2501.03234».ThetaLocalExcursionScales
