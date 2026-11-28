import ThetaResonantPrefix
import ThetaResonanceScales

/-! Any large prime below a fixed positive logarithmic theta slope has an exceptional
ordinary reciprocal exponential sum on an intermediate scale. -/
namespace Arxiv.«2501.03234».ThetaReciprocalResonance
open Filter Real Asymptotics ThetaResonanceScales ThetaResonantBlock ThetaResonantPrefix
open ThetaReciprocalPrefixes ThetaReciprocalCutoff
noncomputable section

def window (p N : ℕ) (δ : ℝ) : Prop :=
  exp (sqrt (log p)/512) ≤ N ∧ (N:ℝ) ≤ (p:ℝ)^(3/4+δ) ∧ N<p

def signal {p : ℕ} [Fact p.Prime] (N : ℕ) (a : ZMod p) : Prop :=
  (N:ℝ)/(134217728*log N*log (log N)) < ‖recipSum N a‖

theorem upper_scale {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ p : ℕ in atTop, ∀ i N : ℕ, i<depth p → (depth p:ℝ) ≤ 2*log p →
      (2:ℝ)^i ≤ 4096*((i:ℝ)+1)*discrepancy p → N ≤ 4*2^i →
      (N:ℝ) ≤ (p:ℝ)^(3/4+δ) := by
  have hl := ((isLittleO_log_rpow_rpow_atTop 3 hδ).natCast_atTop).bound
    (by norm_num : (0:ℝ)<1/2097152)
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hl,ht.eventually_ge_atTop 1,eventually_ge_atTop 4] with p h hlog hp
  intro i N hi hdep hj hn
  change 1 ≤ log (p:ℝ) at hlog
  have hx : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hv : (0:ℝ) ≤ harmonic (p/2) := by exact_mod_cast (harmonic_pos (by omega : p/2≠0)).le
  have hh : 1+(harmonic (p/2):ℝ) ≤ 3*log p := by
    have hlg := log_le_log (by exact_mod_cast (show 0<p/2 by omega) : 0<((p/2:ℕ):ℝ))
      (show ((p/2:ℕ):ℝ) ≤ p by exact_mod_cast Nat.div_le_self p 2)
    linarith [harmonic_le_one_add_log (p/2)]
  have hi' : (i:ℝ)+1 ≤ 2*log p := (show (i:ℝ)+1 ≤ depth p by exact_mod_cast hi).trans hdep
  have hh' := pow_le_pow_left₀ (by linarith only [hv] : 0 ≤ 1+(harmonic (p/2):ℝ)) hh 2
  have hk : (2:ℝ)^i ≤ 4096*(2*log p)*(4*(p:ℝ)^(3/4:ℝ)*(3*log p)^2) := by
    unfold discrepancy at hj
    apply hj.trans
    gcongr
  have hn' : (N:ℝ) ≤ 4*(2:ℝ)^i := by exact_mod_cast hn
  change ‖(log (p:ℝ))^(3:ℝ)‖ ≤ (1/2097152:ℝ)*‖(p:ℝ)^δ‖ at h
  rw [show (3:ℝ)=(3:ℕ) by norm_num,rpow_natCast,Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (rpow_nonneg hx.le _)] at h
  rw [rpow_add hx]
  have hb := mul_le_mul_of_nonneg_left h (rpow_nonneg hx.le (3/4:ℝ))
  have hpℓ : 0 ≤ (p:ℝ)^(3/4:ℝ)*(log p)^3 := by positivity
  nlinarith only [hk,hn',hb,hpℓ]

/-- A small original theta value forces a substantial ordinary initial reciprocal sum.
The lower length is super-polylogarithmic and the upper endpoint uses only the
elementary three-quarter-power Kloosterman bound. -/
theorem witness {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        ∃ N : ℕ,window p N δ ∧ ∃ a : ZMod p,a≠0 ∧ signal N a := by
  filter_upwards [scales,upper_scale hδ] with p h hupper
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  obtain ⟨hp₀,hs₀,hsmall,hst,ht₀,hfit,hdepth,hroot⟩ := h
  have hpr := Nat.odd_iff.mp ho
  obtain ⟨i,hs,ht,hblock⟩ := large_tile ht₀ hst hsmall (by omega)
    (small_sum_forces_triangle hpr hp₀ hS)
  obtain ⟨hJ,N,hlo,hhi,hn,a,ha,he⟩ := resonant_prefix hpr (by omega) hblock
  obtain ⟨hlen,hv,hi⟩ := length_lower hs hs₀ hroot hlo
  exact ⟨N,⟨hlen,hupper i N ht hdepth hJ hhi,hn⟩,a,ha,strength hhi hi hv he⟩

/-- Uniform reciprocal cancellation on this window yields the pinned lower-growth
conclusion for every fixed multiplier. -/
theorem pinned_growth {δ : ℝ} (hδ : 0<δ)
    (hcancel : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ N : ℕ,window p N δ → ∀ a : ZMod p,a≠0 → ¬signal N a)
    (n : ℕ) : type_of% (conjecture_4_4 n) := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [witness hδ,hcancel,ht.eventually_gt_atTop (100*(n:ℝ))] with p h he hlog
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hlarge : (p:ℝ)*log p/100 < (S p:ℝ) := by
    by_contra! hsmall
    obtain ⟨N,hw,a,ha,hN⟩ := h hp ho hsmall
    exact he hp ho N hw a ha hN
  change 100*(n:ℝ) < log (p:ℝ) at hlog
  have hx := mul_lt_mul_of_pos_right hlog (Nat.cast_pos.mpr hp.pos : 0<(p:ℝ))
  exact_mod_cast (show (n:ℝ)*(p:ℝ)<(S p:ℝ) by linarith)

#print axioms witness
#print axioms pinned_growth
end
end Arxiv.«2501.03234».ThetaReciprocalResonance
