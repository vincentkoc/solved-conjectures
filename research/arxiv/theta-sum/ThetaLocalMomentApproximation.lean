import ThetaLocalMomentBudgets
import ThetaPrimeQuantiles

/-! A common logarithmic row model approximates the original residual in
each fixed power mean, uniformly in the short-interval length. -/
namespace Arxiv.«2501.03234».ThetaLocalMomentApproximation
open Real Filter Finset ThetaLocalMomentScales ThetaLocalPrimeCounts ThetaLocalResidualEnergy
open ThetaLocalCenteredApproximation ThetaLocalModelError ThetaPrimeLaw ThetaCharacterPrimeMeans
open ThetaPrimeMeanSquare ThetaCalibratedCone ThetaLocalVanishingCone ThetaDiagonalConstant ThetaIdentityModels
open ThetaReciprocalInversion ThetaDenominatorTails ThetaShortPrimeInterval
noncomputable section

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ {X Y N H : ℕ}, 1≤log (X:ℝ) →
    2≤Y → Y≤X → H≤X → ∀ p∈sample X H,
      |residual p-residualModel Y N p|≤C*(log X)^2 := by
  obtain ⟨M,hM,hm⟩ := ThetaPrimeQuantiles.pointwise
  let c := 8/π^2
  have hc : 0<c := by dsimp [c]; positivity
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  refine ⟨4*M+|diagonalConstant|+12*c*Z,by positivity,?_⟩
  intro X Y N H hL hY hYX hHX p hp
  obtain ⟨hi,hpr,_⟩ := mem_primes.mp hp
  obtain ⟨_,hy⟩ := mem_Ioc.mp hi
  have hx : 0<(X:ℝ) := by exact_mod_cast (by omega : 0<X)
  have hlog : log ((2*X:ℕ):ℝ)=log 2+log X := by push_cast;rw [log_mul (by norm_num) hx.ne']
  have hll : 1≤log ((2*X:ℕ):ℝ) := by rw [hlog];linarith only [hL,log_two_gt_d9]
  have h₂ := hm (2*X) p hll hpr (by omega)
  change |residual p|≤M*(log ((2*X:ℕ):ℝ))^2 at h₂
  have hup := pow_le_pow_left₀ (zero_le_one.trans hll)
    (show log ((2*X:ℕ):ℝ)≤2*log X by rw [hlog];linarith only [log_two_lt_d9,hL]) 2
  have hypos : 1≤(Y:ℝ) := by exact_mod_cast (show 1≤Y by omega)
  have hyl := log_le_log (zero_lt_one.trans_le hypos) (by exact_mod_cast hYX : (Y:ℝ)≤X)
  have h₃ := pow_le_pow_left₀ (by linarith only [log_nonneg hypos] : 0≤1+log (Y:ℝ))
    (show 1+log (Y:ℝ)≤2*log X by linarith only [hyl,hL]) 2
  have hmodel := height (by omega : 1≤Y) N p
  have hb := abs_add_le diagonalConstant (c*ThetaPrimeTailTransfer.model Y N p)
  rw [abs_mul,abs_of_pos hc] at hb
  have h := abs_sub (residual p) (residualModel Y N p)
  change |residual p-residualModel Y N p|≤|residual p|+|residualModel Y N p| at h
  change |residualModel Y N p|≤_ at hb
  nlinarith only [h,h₂,hb,mul_le_mul_of_nonneg_left hup hM.le,
    mul_le_mul_of_nonneg_left hmodel hc.le,mul_le_mul_of_nonneg_left h₃ (show 0≤3*c*Z by positivity),
    mul_le_mul_of_nonneg_left (one_le_pow₀ hL (n:=2)) (abs_nonneg diagonalConstant)]

private theorem split_bound {x v U F t : ℝ} (k : ℕ) (hv : 0≤v) (hU : |x|≤U) (ht : 0<t)
    (hgood : F≤t → |x|≤v) : |x|^k≤v^k+U^k/t^2*F^2 := by
  have hu := (abs_nonneg x).trans hU
  by_cases h : F≤t
  · exact (pow_le_pow_left₀ (abs_nonneg x) (hgood h) k).trans (le_add_of_nonneg_right (by positivity))
  · have hs := pow_le_pow_left₀ ht.le (le_of_not_ge h) 2
    apply (pow_le_pow_left₀ (abs_nonneg x) hU k).trans
    have he : U^k/t^2*t^2=U^k := div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')
    linarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0≤U^k/t^2),he,pow_nonneg hv k]

/-- The common model and its period are chosen before the interval length.
The moment is normalized by the ordinary logarithmic-integral mass. -/
theorem powers {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e) {θ : ℝ}
    (hθ : (e:ℝ)/64<θ) (ordinary : Ordinary θ) {k : ℕ} (hk₁ : 1≤k) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, let Y := den (2*k+13) X
    2≤Y ∧ (Y:ℝ)≤(log X)^(64*(2*k+13)) ∧ ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      (∑ p∈sample X H,|residual p-residualModel Y N p|^k)≤ε*mass X H := by
  obtain ⟨B,hB,hv⟩ := high_rows he h48
  obtain ⟨C,hC,hcst⟩ := uniform_bound
  let c := 8/π^2
  have hcp : 0<c := by dsimp [c]; positivity
  let v := min 1 (ε/4)
  let t := v/(3*c)
  have hvp : 0<v := lt_min (by norm_num) (by positivity)
  have htp : 0<t := by dsimp [t];positivity
  have htval : c*t=v/3 := by dsimp [t];field_simp
  obtain ⟨N₀,ha⟩ := eventually_atTop.mp (signed he h48 hk (show 0<v/3 by positivity))
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ThetaLocalMomentBudgets.scales hθ hB (2*k+1) (max 2 N₀) htp,
    ThetaLocalMomentBudgets.count ordinary,hl.eventually_ge_atTop (2*C^k/(t^2*ε)),
    hl.eventually_ge_atTop (2:ℝ)] with X hs hcnt hhx hlog
  obtain ⟨N,hn,h₂,hy,hlo,hhi,hY,hsmall,hbudget⟩ := hs
  let Y := den (2*k+13) X
  let L := log (X:ℝ)
  have hN := (le_max_left 2 N₀).trans hn
  have hN₀ := (le_max_right 2 N₀).trans hn
  change 2≤Y at h₂
  change 3*(Y:ℝ)/N≤t at hsmall
  change 2≤L at hlog
  have hLp : 0<L := by linarith
  let K := coneWindow (coneWidth N)
  let F := windowExtension (above Y K) (2*fine e N)
  refine ⟨N,h₂,hY,?_⟩
  intro H hHX hlen
  obtain ⟨hM,hcard⟩ := hcnt H hHX hlen
  let M := mass X H
  have hV := (sample_energy F X H).trans (hv hN h₂ (X+1) H K)
  have hE := hV.trans (hbudget H hHX hlen)
  change (∑ p∈sample X H,‖F p‖^2)≤M/L^(2*k+1) at hE
  let U := C*L^2
  have hpow (p : ℕ) (hp : p∈sample X H) :
      |residual p-residualModel Y N p|^k≤v^k+U^k/t^2*‖F p‖^2 := by
    have hnX := (Nat.le_self_pow (by decide : 56≠0) N).trans hlo
    apply split_bound k hvp.le (hcst (by linarith only [hlog] : 1≤L) h₂ (hy.trans hnX) hHX p hp) htp
    intro hf
    obtain ⟨hi,hpr,_⟩ := mem_primes.mp hp
    obtain ⟨hx,hu⟩ := mem_Ioc.mp hi
    have hh := ha N hN₀ hy hpr (hlo.trans hx.le) (hu.trans (by omega))
    change |residual p-residualModel Y N p|≤v/3+c*(3*(Y:ℝ)/N+‖F p‖) at hh
    linarith only [hh,mul_le_mul_of_nonneg_left (add_le_add hsmall hf) hcp.le,htval]
  apply (sum_le_sum hpow).trans
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
  have hU : 0≤U^k/t^2 := by dsimp [U]; positivity
  have hscale : U^k/t^2*(M/L^(2*k+1))≤ε/2*M := by
    have hEq : U^k/t^2*(M/L^(2*k+1))=C^k/(t^2*L)*M := by
      dsimp [U]; rw [mul_pow,←pow_mul,pow_succ L (2*k)];field_simp
    rw [hEq]
    apply mul_le_mul_of_nonneg_right _ hM.le
    rw [div_le_iff₀ (by positivity)]
    change 2*C^k/(t^2*ε)≤L at hhx
    have h := (div_le_iff₀ (by positivity : 0<t^2*ε)).mp hhx
    linarith only [h]
  have hpowv : v^k≤v := by simpa using pow_le_pow_of_le_one hvp.le (min_le_left ..) hk₁
  have hvε : v≤ε/4 := min_le_right ..
  have hmain := mul_le_mul hcard (hpowv.trans hvε) (pow_nonneg hvp.le _) (by positivity)
  change _≤ε*M
  linarith only [hmain,(mul_le_mul_of_nonneg_left hE hU).trans hscale]

#print axioms powers
end
end Arxiv.«2501.03234».ThetaLocalMomentApproximation
