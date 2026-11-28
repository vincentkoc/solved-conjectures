import Erdos478WindowImageCard
import Erdos478LogarithmicWindowSpan

/-! # Extremal factorial-image size across all positive windows of a given span -/

namespace Erdos478.LocalSpacing
open Filter Finset Topology
open scoped Classical

/-- Attained lower bound across all translates inside the host's positive index set. -/
def SharpSpan (p H : ℕ) : Prop :=
  IsLeast {n : ℕ | ∃ a, 1≤a ∧ a+H<p ∧ (windowValues p a H).card=n} H

private theorem fits {p H : ℕ} (hp : p.Prime) (cut : (H+2)^(H^2)<p) : 1+H<p := by
  rcases Nat.eq_zero_or_pos H with rfl|pos
  · have := hp.two_le
    omega
  · have e : 1≤H^2 := Nat.one_le_pow _ _ pos
    have h := Nat.pow_le_pow_right (by omega : 0<H+2) e
    rw [pow_one] at h
    omega

theorem sharp_iff_pair {p H : ℕ} (hp : p.Prime) (cut : (H+2)^(H^2)<p) :
    SharpSpan p H ↔ ∃ i j, 1 ≤ i ∧ i < j ∧ j<p ∧ j-i≤H ∧ i.factorial%p=j.factorial%p := by
  constructor
  · rintro ⟨⟨a,ha,hu,hc⟩,_⟩
    have hit : hasRepetition p a H := by
      by_contra hn
      rw [window_card_exact hp hu cut,dif_neg hn] at hc
      omega
    obtain ⟨i,j,lo,lt,hi,rep⟩ := hit
    exact ⟨i,j,ha.trans lo,lt,hi.trans_lt hu,by omega,rep⟩
  · rintro ⟨i,j,lo,lt,hi,len,rep⟩
    let a := max 1 (j-H)
    have fits' := fits hp cut
    have ha : 1≤a := le_max_left ..
    have ai : a ≤ i := by dsimp [a]; omega
    have jH : j≤a+H := by dsimp [a]; omega
    have hu : a+H<p := by dsimp [a]; omega
    have hit : hasRepetition p a H := ⟨i,j,ai,lt,jH,rep⟩
    refine ⟨⟨a,ha,hu,?_⟩,?_⟩
    · rw [window_card_exact hp hu cut,dif_pos hit]
    · rintro n ⟨x,_,endx,rfl⟩
      exact (window_card_bounds hp endx cut).1

/-- Every admissible window has at least `H` distinct factorial residues at
the explicit increasing logarithmic span. -/
theorem eventual_window_bounds (c : ℝ) (hc : 0≤c) (hc2 : c^2≤2) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ a, 1≤a → a+logSpan c p<p →
      logSpan c p≤(windowValues p a (logSpan c p)).card ∧
      (windowValues p a (logSpan c p)).card≤logSpan c p+1 := by
  filter_upwards [logSpan_cut c hc hc2] with p cut hp a _ hu
  exact window_card_bounds hp hu cut

/-- Along the same prime filter as the host, every moving window on this
scale has image density tending to one relative to its own length. -/
theorem moving_window_density (a H : ℕ → ℕ) (grow : Tendsto H atTop atTop)
    (cut : ∀ᶠ p : ℕ in atTop, (H p+2)^(H p^2)<p)
    (valid : ∀ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime}, 1≤a p ∧ a p+H p<p) :
    Tendsto (fun p => ((windowValues p (a p) (H p)).card:ℝ)/(H p+1))
      (atTop ⊓ principal {p : ℕ | p.Prime}) (𝓝 1) := by
  have recip := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp ((tendsto_add_atTop_nat 1).comp grow)
  have low : Tendsto (fun p => 1-1/((H p:ℝ)+1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub recip
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (low.mono_left inf_le_left) tendsto_const_nhds
  all_goals
    filter_upwards [cut.filter_mono inf_le_left,valid,
      (show ∀ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime}, p.Prime from
        (eventually_principal.mpr (fun _ hp => hp)).filter_mono inf_le_right)] with p c hv hp
    obtain ⟨lo,hi⟩ := window_card_bounds hp hv.2 c
    have pos : 0<(H p:ℝ)+1 := by positivity
  · apply (le_div_iff₀ pos).mpr
    have h : (H p:ℝ)≤(windowValues p (a p) (H p)).card := by exact_mod_cast lo
    calc (1-1/((H p:ℝ)+1))*((H p:ℝ)+1)=(H p:ℝ) := by field_simp; ring
         _≤_ := h
  · apply (div_le_iff₀ pos).mpr
    simpa using (show ((windowValues p (a p) (H p)).card:ℝ)≤H p+1 by exact_mod_cast hi)

#print axioms moving_window_density
#print axioms SharpSpan
#print axioms sharp_iff_pair
#print axioms eventual_window_bounds
end Erdos478.LocalSpacing
