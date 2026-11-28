import ThetaLocalResidualEnergy

/-! A logarithmic denominator scale and a power band common to every sample
length at a given starting endpoint. -/
namespace Arxiv.«2501.03234».ThetaLocalMomentScales
open Real Filter ThetaLocalExcursionScales ThetaLocalPrimeCounts
noncomputable section

def den (m X : ℕ) := ⌊log (X:ℝ)⌋₊^(64*m)

theorem den_bounds {m : ℕ} (hm : 1≤ m) : ∀ᶠ X : ℕ in atTop,
    let L := log (X:ℝ)
    2≤den m X ∧ (den m X:ℝ)≤L^(64*m) ∧ (((den m X)^2:ℕ):ℝ)≤(X:ℝ)^(1/64:ℝ) ∧
    L^m≤(2:ℝ)^m*(den m X:ℝ)^(1/64:ℝ) := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop 4,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (logs (by norm_num : (0:ℝ)<1/64) (by norm_num : (0:ℝ)<1) (64*m*2))] with X hL hpoly
  let L := log (X:ℝ)
  let k := ⌊L⌋₊
  change 4≤L at hL
  have hl : (k:ℝ)≤L := Nat.floor_le (by linarith)
  have hu : L<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk : (2:ℝ)≤k := by linarith only [hL,hu]
  have hk' : 2≤k := by exact_mod_cast hk
  have hcut : (den m X:ℝ)=(k:ℝ)^(64*m) := by simp [den,k,L]
  have hy := pow_le_pow_left₀ (Nat.cast_nonneg k : 0≤(k:ℝ)) hl (64*m)
  refine ⟨hk'.trans (Nat.le_self_pow (by omega : 64*m≠0) k),by rw [hcut]; exact hy,?_,?_⟩
  · rw [Nat.cast_pow,hcut,←pow_mul]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg k : 0≤(k:ℝ)) hl _).trans (by simpa using hpoly)
  · rw [hcut,←rpow_natCast_mul (Nat.cast_nonneg k),show ((64*m:ℕ):ℝ)*(1/64:ℝ)=m by push_cast;ring,
      rpow_natCast,←mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith only [hu,hk]) m

theorem band {e : ℕ} {θ : ℝ} (hθ : (e:ℝ)/64<θ) {m : ℕ} (hm : 1≤ m) : ∀ᶠ X : ℕ in atTop,
    ∃ N : ℕ, 2≤N ∧ N^56≤X ∧ 2*X≤N^64 ∧ (den m X)^2≤N ∧ log N≤log X ∧
      (N:ℝ)^e*(log X)^m≤(X:ℝ)^θ := by
  let r : ℝ := (e:ℝ)/64
  let C := ((2:ℝ)^65)^r
  have hC : 0<C := by dsimp [C]; positivity
  filter_upwards [den_bounds hm,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (logs (sub_pos.mpr hθ) hC m),
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
    exact_mod_cast hcut.2.2.1.trans h
  · calc _ ≤ (C*(X:ℝ)^r)*(log X)^m := mul_le_mul_of_nonneg_right he (pow_nonneg hL _)
         _ = (X:ℝ)^r*(C*(log X)^m) := by ring
         _ ≤ (X:ℝ)^r*(X:ℝ)^(θ-r) := mul_le_mul_of_nonneg_left htail (rpow_nonneg hx.le _)
         _ = _ := by rw [←rpow_add hx]; congr 1; ring


theorem den_large {m : ℕ} (hm : 1≤ m) : Tendsto (den m) atTop atTop := by
  apply tendsto_atTop_mono (fun (X : ℕ) => Nat.le_self_pow (by omega : 64*m≠0) ⌊log (X:ℝ)⌋₊)
  exact tendsto_nat_floor_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

#print axioms den_bounds
#print axioms band
end
end Arxiv.«2501.03234».ThetaLocalMomentScales
