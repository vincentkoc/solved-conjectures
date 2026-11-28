import ThetaTernaryWindows

/-! Quantitative resilience of each prime triple count at its own central window. -/
namespace Arxiv.«2501.03234».ThetaTernaryTransfer
open Filter Real Finset ThetaTernaryErrorBudget ThetaTernaryWindows ThetaShortPrimeInterval
open ThetaTernaryDeletion ThetaTernaryPacking
noncomputable section
open scoped Classical

def errors (n : ℕ) (θ ε : ℝ) := (window n θ).filter (bad ε)
def selected (n : ℕ) (θ ε : ℝ) := window n θ \ errors n θ ε

theorem mem_selected {n p : ℕ} {θ ε : ℝ} :
    p∈selected n θ ε ↔ p∈window n θ ∧ |(S p:ℝ)-p*log p/2| < ε*p*log p := by
  by_cases h : p∈window n θ <;> simp [selected,errors,bad,h]

/-- Local scarcity of theta exceptions at every fixed log power. -/
def Control (θ : ℝ) : Prop := ∀ {ε δ : ℝ}, 0<ε → 0<δ → ∀ m : ℕ,
    ∀ᶠ n : ℕ in atTop, (0<width n ∧ 0<(n:ℝ)^θ) ∧
      ((window n θ).card:ℝ)≤8*(n:ℝ)^θ ∧
      (((errors n θ ε).card:ℝ)+1)*(width n)^m ≤ δ*(n:ℝ)^θ

theorem of_power {α θ : ℝ} (hα : 0≤α) (hθ : α<θ) (ht : θ<1) (hex : ExceptionalPower α) :
    Control θ := by
  intro ε δ hε hδ m
  let σ := δ/(8*2^m)
  have hσ : 0<σ := by dsimp [σ];positivity
  obtain ⟨K,hK,h⟩ := thin hα hex hε hσ m
  obtain ⟨X₀,h₀⟩ := eventually_atTop.mp h
  filter_upwards [scales hα hθ ht m hK X₀,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 1]
    with n hs hn
  obtain ⟨X,H,hX,hHX,hfit,hH,hw,hV,hcontain⟩ := hs
  have hE := h₀ X hX H hfit hHX
  have hsub : errors n θ ε ⊆ primes X H (bad ε) := by
    intro p hp
    obtain ⟨ha,he⟩ := Finset.mem_filter.mp hp
    exact mem_primes.mpr ⟨hcontain p ha,(Nat.mem_primesLE.mp (Finset.mem_filter.mp ha).1).2,he⟩
  have hw' : 0<width n := by unfold width;linarith only [log_nonneg hn]
  have hcount : (window n θ).card≤H := by
    apply (card_le_card (show window n θ ⊆ Ioc X (X+H) from fun p hp => hcontain p hp)).trans
    simp
  refine ⟨⟨hw',rpow_pos_of_pos (by linarith) _⟩,(Nat.cast_le.mpr hcount).trans hH,?_⟩
  have h₁ := pow_le_pow_left₀ hw'.le hw m
  rw [mul_pow] at h₁
  have h₂ := Nat.cast_le (α:=ℝ).mpr (card_le_card hsub)
  have h₃ : 0<((primes X H (bad ε)).card:ℝ)+1 := by positivity
  calc _ ≤ (((primes X H (bad ε)).card:ℝ)+1)*((2:ℝ)^m*(width X)^m) :=
            mul_le_mul (by linarith only [h₂]) h₁ (pow_nonneg hw'.le _) h₃.le
       _ = (2:ℝ)^m*((((primes X H (bad ε)).card:ℝ)+1)*(width X)^m) := by ring
       _ ≤ (2:ℝ)^m*(σ*(8*(n:ℝ)^θ)) :=
            mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left hH hσ.le)) (by positivity)
       _ = _ := by dsimp [σ];field_simp

/-- The loss from excluding theta errors and repeated primes at a fixed sum is
smaller than (n^θ)^2 divided by every fixed log power, uniformly in that sum. -/
theorem original {θ ε δ : ℝ} (control : Control θ) (hε : 0<ε) (hδ : 0<δ) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ z : ℕ,
      ((triples (window n θ) (window n θ) (window n θ) z).card:ℝ) ≤
        (distinctTriples (selected n θ ε) z).card+δ*((n:ℝ)^θ)^2/(width n)^m := by
  filter_upwards [control hε (show 0<δ/24 by positivity) m] with n hb z
  obtain ⟨⟨hV,hR⟩,hA,hE⟩ := hb
  let A := window n θ
  let E := errors n θ ε
  let R := (n:ℝ)^θ
  let V := (width n)^m
  have hv : 0<V := pow_pos hV _
  have h := distinct_deletion A E z
  have hnat : ((triples A A A z).card:ℝ) ≤ (distinctTriples (selected n θ ε) z).card+
      3*((E.card:ℝ)+1)*A.card := by exact_mod_cast h
  apply hnat.trans (add_le_add le_rfl _)
  apply (le_div_iff₀ hv).mpr
  have hcard : 0≤((E.card:ℝ)+1)*V := by positivity
  change ((E.card:ℝ)+1)*V≤δ/24*R at hE
  change (A.card:ℝ)≤8*R at hA
  have hprod := mul_le_mul hE hA (Nat.cast_nonneg _) (mul_nonneg (by positivity) hR.le)
  change 3*((E.card:ℝ)+1)*A.card*V ≤ δ*R^2
  linarith only [hprod]

/-- Unconditional loss bound for the original signed sum in every central window
above exponent 3/4, uniformly over every target sum. -/
theorem elementary_loss {θ ε δ : ℝ} (hθ : 3/4<θ) (ht : θ<1) (hε : 0<ε) (hδ : 0<δ) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ z : ℕ,
      ((triples (window n θ) (window n θ) (window n θ) z).card:ℝ) ≤
        (distinctTriples (selected n θ ε) z).card+δ*((n:ℝ)^θ)^2/(width n)^m :=
  original (of_power (by norm_num) hθ ht ThetaShortPrimeInterval.elementary) hε hδ m

#print axioms mem_selected
#print axioms elementary_loss
#print axioms of_power
#print axioms original
end
end Arxiv.«2501.03234».ThetaTernaryTransfer
