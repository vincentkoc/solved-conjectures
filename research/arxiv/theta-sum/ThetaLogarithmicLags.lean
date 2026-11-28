import ThetaPrimeLagBounds
import ThetaLocalExcursionScales

/-! A positive signed pair correlation and a fourth-order displacement
energy already occur on the logarithmic prime-spacing scale. -/
namespace Arxiv.«2501.03234».ThetaLogarithmicLags
open Real Filter Finset ThetaPositiveLag ThetaPrimeLagBounds
open scoped Topology
noncomputable section

private theorem extract {X q L : ℕ} {c : ℝ} (hc : 0<c) (hX : 2≤X) (hL : 0<L) (g : ℕ → ℝ)
    (h : c*X*L≤(∑ k∈offsets L,max 0 (corr X (q*k) g))*(log X)^2) :
    (∃ k∈offsets L,c*X≤corr X (q*k) g*(log X)^2) ∧
    c^2*(X:ℝ)^2*L≤(∑ k∈offsets L,(corr X (q*k) g)^2)*(log X)^4 := by
  have hx : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl : 0<(L:ℝ) := by exact_mod_cast hL
  have hlog := log_pos (show (1:ℝ)<X by exact_mod_cast hX)
  have hnum : (offsets L).card=L-1 := by
    rw [offsets,card_erase_of_mem (mem_range.mpr hL),card_range]
  constructor
  · by_contra! hh
    have h₁ (k : ℕ) (hk : k∈offsets L) : max 0 (corr X (q*k) g)*(log X)^2≤c*X := by
      rcases le_total 0 (corr X (q*k) g) with he|he
      · rw [max_eq_right he];exact (hh k hk).le
      · rw [max_eq_left he,zero_mul];positivity
    have hs := sum_le_sum h₁
    simp only [←sum_mul,sum_const,nsmul_eq_mul,hnum] at hs
    have hlt : ((L-1:ℕ):ℝ)<L := by exact_mod_cast (show L-1<L by omega)
    nlinarith only [hs,h,mul_lt_mul_of_pos_right hlt (mul_pos hc hx)]
  · have hs := square (X+1) q L (cut X g)
    simp only [mass,energy,cut_lag] at hs
    have hh := pow_le_pow_left₀ (by positivity : 0≤c*X*L) h 2
    apply (mul_le_mul_iff_right₀ hl).mp
    nlinarith only [hh,mul_le_mul_of_nonneg_right hs (show 0≤(log X)^4 by positivity)]

theorem summary {q : ℕ} (_hq : 0<q) {c : ℝ} (hc : 0<c) {g : ℕ → ℝ} (s : Scales q c g) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,∀ L : ℕ,K*log X≤L → q*L≤X →
      (∃ k∈offsets L,c*X≤corr X (q*k) g*(log X)^2) ∧
      c^2*(X:ℝ)^2*L≤(∑ k∈offsets L,(corr X (q*k) g)^2)*(log X)^4 := by
  obtain ⟨K,hK,h⟩ := s
  refine ⟨K,hK,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with X hh hx
  intro L hl ht
  have hlog := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
  exact extract hc hx (Nat.cast_pos.mp ((mul_pos hK hlog).trans_le hl)) g (hh L hl ht)

theorem short {q : ℕ} (hq : 0<q) {c : ℝ} (hc : 0<c) {g : ℕ → ℝ} (s : Scales q c g) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop,∃ h : ℕ,0<h ∧ q∣h ∧ (h:ℝ)≤A*log X ∧
      c*X≤corr X h g*(log X)^2 := by
  obtain ⟨K,hK,H⟩ := summary hq hc s
  let A := (q:ℝ)*(K+1)
  have ha : 0<A := by dsimp [A];positivity
  refine ⟨A,ha,?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hcap := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (ThetaLocalExcursionScales.logs (by norm_num : (0:ℝ)<1) ha 1)
  filter_upwards [H,hcap,hlog.eventually_ge_atTop 1] with X hx hcap hl
  change (1:ℝ)≤log X at hl
  let L := ⌈K*log X⌉₊
  have hlow : K*log X≤L := Nat.le_ceil _
  have hu : (L:ℝ)≤(K+1)*log X := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg hK.le (zero_le_one.trans hl))
    change (⌈K*log X⌉₊:ℝ)≤_;linarith only [hh,hl]
  have hqL : (q*L:ℕ)≤X := by
    have h := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg q)
    have h' : A*log X≤X := by simpa only [pow_one,rpow_one] using hcap
    dsimp only [A] at h';exact_mod_cast (show (q:ℝ)*L≤X by nlinarith only [h,h'])
  obtain ⟨k,hk,hcorr⟩ := (hx L hlow hqL).1
  obtain ⟨hk₀,hk'⟩ := mem_erase.mp hk
  have hbig := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (mem_range.mp hk').le) (Nat.cast_nonneg (α:=ℝ) q)
  refine ⟨q*k,Nat.mul_pos hq (Nat.pos_of_ne_zero hk₀),dvd_mul_right ..,?_,hcorr⟩
  push_cast;dsimp only [A];nlinarith only [hbig,mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α:=ℝ) q)]

#print axioms summary
#print axioms short
end
end Arxiv.«2501.03234».ThetaLogarithmicLags
