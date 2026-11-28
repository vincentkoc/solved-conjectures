import ThetaLowMultiplierLevel
import ThetaResonantLengths

/-! Small signed integer multipliers on the full range of resonant levels. -/
namespace Arxiv.«2501.03234».ThetaShortMultiplier
open Finset Filter Real Asymptotics ThetaShortFrequencies ThetaLowMultiplierLevel
open ThetaResonanceScales ThetaResonantBlock ThetaResonantPrefix ThetaResonantCount
open ThetaReciprocalResonance ThetaResonantLengths
noncomputable section

def shortSignal {p : ℕ} [Fact p.Prime] (N : ℕ) : Prop :=
  ∃ j : ℤ, (j:ZMod p)/4≠0 ∧ |(j:ℝ)| ≤ 2199023255552*(N:ℝ)*(log N)^2 ∧
    signal N ((j:ZMod p)/4)

def smallLengths (p : ℕ) [Fact p.Prime] (δ : ℝ) : Finset ℕ := by
  classical
  exact (range p).filter fun N => window p N δ ∧ shortSignal (p:=p) N

private theorem fit : ∀ᶠ p : ℕ in atTop,∀ i<depth p, cutoff i ≤ p/2 := by
  have hl := ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)).natCast_atTop).bound
    (by norm_num : (0:ℝ)<1/137438953472)
  filter_upwards [hl,scales] with p h H
  intro i hi
  have hdep := H.2.2.2.2.2.2.1
  have hI : (i:ℝ)+1 ≤ 2*log p := (show (i:ℝ)+1≤depth p by exact_mod_cast hi).trans hdep
  change ‖(log (p:ℝ))^(2:ℝ)‖ ≤ (1/137438953472:ℝ)*‖(p:ℝ)^(1:ℝ)‖ at h
  rw [show (2:ℝ)=(2:ℕ) by norm_num,rpow_natCast,rpow_one,Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)] at h
  have hx := pow_le_pow_left₀ (by positivity : 0≤(i:ℝ)+1) hI 2
  have htwo : 2*cutoff i ≤ p := by
    dsimp [cutoff]
    exact_mod_cast (show 2*(4*(65536*((i:ℝ)+1))^2) ≤ p by nlinarith only [hx,h])
  omega

theorem small_at_level {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ i∈levels p (lowerLevel p) (depth p), ∃ N∈smallLengths p δ, 2^i≤N ∧ N≤4*2^i := by
  classical
  filter_upwards [fit,scales,upper_scale hδ] with p hfit H hupper
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro i him
  obtain ⟨hm,hb⟩ := mem_filter.mp him
  obtain ⟨hs,ht⟩ := mem_Ico.mp hm
  obtain ⟨_,hs₀,_,_,_,hfit',hdepth,hroot⟩ := H
  have hpr := Nat.odd_iff.mp ho
  obtain ⟨N,hlo,hhi,hn,c,hc,hnear,he⟩ := short_prefix hpr (hfit i ht) hb
  have hJ := (resonant_prefix hpr (by omega) hb).1
  obtain ⟨hlen,hv,hi⟩ := length_lower hs hs₀ hroot hlo
  have hsig := strength hhi hi hv he
  obtain ⟨d,hd,hpos⟩ := hnear
  have hh : (d:ℝ) ≤ 2199023255552*(N:ℝ)*(log N)^2 := by
    have hcast : (d:ℝ) ≤ 8*(2:ℝ)^i*(4*(65536*((i:ℝ)+1))^2) := by exact_mod_cast hd
    have hlo' : (2:ℝ)^i ≤ N := by exact_mod_cast hlo
    have hi' := pow_le_pow_left₀ (by positivity : 0≤(i:ℝ)+1) hi 2
    have h1 := mul_le_mul_of_nonneg_left hi' (show 0≤(2:ℝ)^i by positivity)
    have h2 := mul_le_mul_of_nonneg_right hlo' (sq_nonneg (log (N:ℝ)))
    nlinarith only [hcast,h1,h2]
  have htwo := (ThetaFourier.two_unit hpr).ne_zero
  have hfour : (4:ZMod p)≠0 := by rw [show (4:ZMod p)=2*2 by norm_num];exact mul_ne_zero htwo htwo
  have short (j : ℤ) (hj : (j:ZMod p)=4*c) (hmag : |(j:ℝ)|≤2199023255552*(N:ℝ)*(log N)^2) :
      shortSignal (p:=p) N := by
    refine ⟨j,div_ne_zero (hj ▸ mul_ne_zero hfour hc) hfour,hmag,?_⟩
    rw [hj,mul_div_cancel_left₀ _ hfour]
    exact hsig
  have hcert : shortSignal (p:=p) N := by
    rcases hpos with h|h
    · apply short d (by simpa using h.symm)
      simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)] using hh
    · apply short (-(d:ℤ)) (by simpa using h.symm)
      simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)] using hh
  exact ⟨N,mem_filter.mpr ⟨mem_range.mpr hn,⟨hlen,hupper i N ht hdepth hJ hhi,hn⟩,hcert⟩,hlo,hhi⟩

theorem witness {δ : ℝ} (hδ : 0<δ) : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    (S p:ℝ) ≤ (p:ℝ)*log p/100 → ∃ N : ℕ, window p N δ ∧ shortSignal (p:=p) N := by
  classical
  filter_upwards [small_at_level hδ,scales] with p h H
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  obtain ⟨hp₀,hs₀,hsmall,hst,ht₀,_,_,_⟩ := H
  obtain ⟨i,hs,ht,hb⟩ := large_tile ht₀ hst hsmall (by omega) (small_sum_forces_triangle (Nat.odd_iff.mp ho) hp₀ hS)
  obtain ⟨N,hN,_,_⟩ := h hp ho i (mem_filter.mpr ⟨mem_Ico.mpr ⟨hs,ht⟩,hb⟩)
  exact ⟨N,(mem_filter.mp hN).2⟩

#print axioms small_at_level
#print axioms witness
end
end Arxiv.«2501.03234».ThetaShortMultiplier
