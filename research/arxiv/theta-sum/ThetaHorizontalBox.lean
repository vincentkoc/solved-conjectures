import ThetaManyShortMultipliers
import ThetaHorizontalWitness

/-! A small prime theta sum requires many simultaneous horizontal reciprocal sums
with both variables below the completion scale. -/
namespace Arxiv.«2501.03234».ThetaHorizontalBox
open Finset Filter Real Asymptotics ThetaHorizontalWitness ThetaAdditiveReciprocity
open ThetaManyShortMultipliers ThetaResonantLengths ThetaShortMultiplier ThetaBourgainGaraev
open ThetaSquareRootWindow ThetaReciprocalResonance
noncomputable section

private theorem absorb {α β : ℝ} (hα : 0<α) (hβ : α<β) :
    ∀ᶠ u : ℝ in atTop, 2199023255552*u^2*exp (-u^β) ≤ exp (-u^α) := by
  have h₁ := (tendsto_rpow_atTop (sub_pos.mpr hβ)).eventually_ge_atTop 2
  have h₂ := (isLittleO_log_rpow_atTop (hα.trans hβ)).bound (by norm_num : (0:ℝ)<1/8)
  have ht := tendsto_rpow_atTop (hα.trans hβ)
  filter_upwards [h₁,h₂,ht.eventually_ge_atTop 164,eventually_ge_atTop (1:ℝ)] with u h1 h2 h3 hu
  have hpos : 0<u := by linarith
  change 2 ≤ u^(β-α) at h1
  have hsmall := mul_le_mul_of_nonneg_left h1 (rpow_nonneg hpos.le α)
  rw [←rpow_add hpos,add_sub_cancel] at hsmall
  change ‖log u‖ ≤ (1/8:ℝ)*‖u^β‖ at h2
  simp only [Real.norm_of_nonneg (rpow_nonneg hpos.le _),Real.norm_of_nonneg (log_nonneg hu)] at h2
  have hc : log (2199023255552:ℝ) ≤ 41 := by
    rw [show (2199023255552:ℝ)=(2:ℝ)^41 by norm_num,log_pow]
    norm_num
    linarith [log_two_lt_d9]
  change 164 ≤ u^β at h3
  apply (log_le_log_iff (by positivity) (exp_pos _)).mp
  rw [log_exp,log_mul (by positivity) (exp_ne_zero _),log_mul (by norm_num) (by positivity),log_exp,log_pow]
  push_cast
  linarith

def boxFamily (p : ℕ) (B α b : ℝ) : Prop :=
  ∃ E : Finset ℕ, separated E ∧ b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card ∧
    ∀ N∈E, exp (sqrt (log p)/512) ≤ N ∧ N<p ∧
      ∃ j : ℤ, j≠0 ∧ |(j:ℝ)|≤2199023255552*(N:ℝ)*(log N)^2 ∧
        max (N:ℝ) |(j:ℝ)| ≤ B*exp (-(log p)^α) ∧
        (N:ℝ)/(268435456*log N*log (log N)) < ‖horizontal p N j‖

theorem many (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        boxFamily p ((p:ℝ)^((3:ℝ)/4)) α b ∧
          (letI : Fact p.Prime := ⟨hp⟩; CompleteEstimate p → boxFamily p (sqrt p) α b) := by
  classical
  obtain ⟨b,hb,H⟩ := below estimate
  refine ⟨b,hb,?_⟩
  intro α hα htop
  obtain ⟨β,hβ,hβ'⟩ := exists_between htop
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [H β (hα.trans hβ) hβ',transfer,hlog.eventually (absorb hα hβ),
    hlog.eventually_ge_atTop 1] with p h ht hfac hu
  intro hp ho hS
  let : Fact p.Prime := ⟨hp⟩
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  obtain ⟨he,hw⟩ := h hp ho hS
  have convert (B : ℝ) (hB : 0≤B) (hF : ThetaManyShortMultipliers.family p B β b) :
      boxFamily p B α b := by
    obtain ⟨E,hE,hsep,hcap,hcard⟩ := hF
    refine ⟨E,hsep,hcard,?_⟩
    intro N hn
    obtain ⟨_,hwin,hshort⟩ := mem_filter.mp (hE hn)
    obtain ⟨j,hj,hjN,hjS⟩ := ht hp ho N hwin.1 hwin.2.2 hshort
    refine ⟨hwin.1,hwin.2.2,j,hj,hjN,max_le_iff.mpr ⟨?_,?_⟩,hjS⟩
    · apply (hcap N hn).trans
      gcongr
    · have hN : 0<(N:ℝ) := (exp_pos _).trans_le hwin.1
      have hNat : 1≤N := by exact_mod_cast (show 0<N by exact_mod_cast hN)
      have hlogN := log_le_log hN (show (N:ℝ)≤p by exact_mod_cast hwin.2.2.le)
      have hs := pow_le_pow_left₀ (log_nonneg (by exact_mod_cast hNat)) hlogN 2
      calc
        _ ≤ 2199023255552*(B*exp (-(log p)^β))*(log p)^2 :=
          hjN.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hcap N hn) (by norm_num)) hs
            (sq_nonneg _) (by positivity))
        _ = B*(2199023255552*(log p)^2*exp (-(log p)^β)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hfac hB
  exact ⟨convert _ (rpow_nonneg hx.le _) he,fun hK => convert _ (sqrt_nonneg _) (hw hK)⟩

theorem growth {δ : ℝ} (hδ : 0<δ)
    (noLarge : ∀ᶠ p : ℕ in atTop,∀ _hp : p.Prime, _root_.Odd p →
      ∀ N : ℕ, window p N δ → ¬ horizontalSignal p N) (n : ℕ) : type_of% (conjecture_4_4 n) := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ThetaHorizontalWitness.witness hδ,noLarge,hlog.eventually_gt_atTop (100*(n:ℝ))]
    with p h he hu
  intro hp ho
  have hS : (p:ℝ)*log p/100 < (S p:ℝ) := by
    by_contra! hsmall
    obtain ⟨N,hw,hs⟩ := h hp ho hsmall
    exact he hp ho N hw hs
  change 100*(n:ℝ) < log (p:ℝ) at hu
  have hh := mul_lt_mul_of_pos_right hu (Nat.cast_pos.mpr hp.pos : 0<(p:ℝ))
  exact_mod_cast (show (n:ℝ)*(p:ℝ)<(S p:ℝ) by linarith)

#print axioms many
#print axioms growth
end
end Arxiv.«2501.03234».ThetaHorizontalBox
