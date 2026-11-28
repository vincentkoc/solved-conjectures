import ThetaShortMultiplier
import ThetaSubcriticalResonance

/-! A sign obstruction at many separated lengths with short signed multipliers. -/
namespace Arxiv.«2501.03234».ThetaManyShortMultipliers
open Finset Real Filter ThetaManyReciprocalSums ThetaResonantLengths ThetaResonanceScales
open ThetaResonantCount ThetaShortMultiplier ThetaReciprocalResonance
open ThetaSubcriticalResonance ThetaBourgainGaraev ThetaSquareRootWindow
noncomputable section

theorem small_subset (p : ℕ) [Fact p.Prime] (δ : ℝ) : smallLengths p δ ⊆ lengths p δ := by
  classical
  intro N hN
  obtain ⟨hn,hw,j,hj,_,h⟩ := mem_filter.mp hN
  exact mem_filter.mpr ⟨hn,hw,_,hj,h⟩

theorem many (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧ ∀ δ : ℝ, 0<δ →
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 → ∃ E : Finset ℕ, E ⊆ smallLengths p δ ∧ separated E ∧
        b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card := by
  obtain ⟨c,hc,H⟩ := many_levels estimate
  refine ⟨c/3,by positivity,?_⟩
  intro δ hδ
  filter_upwards [H,small_at_level hδ] with p hsize hsel
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  obtain ⟨E,hE,hs,hcard⟩ := select_lengths _ _ (hsel hp ho)
  refine ⟨E,hE,hs,?_⟩
  have h : ((levels p (lowerLevel p) (depth p)).card:ℝ) ≤ 3*(E.card:ℝ) := by exact_mod_cast hcard
  have ht := (hsize hp ho hS).trans h
  calc
    _ = (c*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3))/3 := by ring
    _ ≤ _ := (div_le_iff₀ (by norm_num)).mpr (by linarith only [ht])

def family (p : ℕ) [Fact p.Prime] (B α b : ℝ) : Prop :=
  ∃ E : Finset ℕ, E ⊆ smallLengths p 1 ∧ separated E ∧
    (∀ n∈E, (n:ℝ) ≤ B*exp (-(log p)^α)) ∧
    b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card

theorem below (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        family p ((p:ℝ)^((3:ℝ)/4)) α b ∧ (CompleteEstimate p → family p (sqrt p) α b) := by
  obtain ⟨c,hc,H⟩ := many estimate
  refine ⟨c/2,by positivity,?_⟩
  intro α hα htop
  have hh := trim (fun p _ => smallLengths p 1) (fun p _ => small_subset p 1) hc (H 1 (by norm_num))
  filter_upwards [hh α hα htop] with p h
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hsmall
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  exact ⟨h hp ho _ (rpow_pos_of_pos hx _) ThetaReciprocalCutoff.kloosterman_bound hsmall,
    fun hK => h hp ho _ (sqrt_pos.mpr hx) hK hsmall⟩

#print axioms many
#print axioms below
end
end Arxiv.«2501.03234».ThetaManyShortMultipliers
