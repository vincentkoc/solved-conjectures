import Erdos478GapSieve
import Erdos478PrimeProportions

/-!
# Ordinary prime proportions for the finite factorial-gap sieve

The ordinary prime ideal theorem is the sole analytic input to this module.
The supplemental adapter supplies its independently checked proof.
-/

namespace Erdos478.GapSieve
noncomputable section
open Finset Filter Topology GapDensity GapVariance MeanDeficit

/-- Proportion of rational primes at most X satisfying P. -/
def fraction (X : ℕ) (P : ℕ → Prop) : ℝ := by
  classical exact (((Nat.primesLE X).filter P).card : ℝ) / (Nat.primesLE X).card

private theorem ordinary_eq (X : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ordinary X (fun p => if P p then 1 else 0) = fraction X P := by
  classical
  change (Nat.primeCounting X : ℝ)⁻¹*(∑ p ∈ Nat.primesLE X, if P p then 1 else 0) = _
  rw [fraction,← Nat.primesLE_card_eq_primeCounting,div_eq_inv_mul]
  congr 1
  rw [card_filter]
  push_cast
  rfl

private theorem fraction_compl (X : ℕ) (hX : 0 < (Nat.primesLE X).card) (P : ℕ → Prop) :
    fraction X P + fraction X (fun p => ¬P p) = 1 := by
  classical
  rw [fraction,fraction,← add_div,← Nat.cast_add,card_filter_add_card_filter_not,
    div_self (by exact_mod_cast hX.ne')]

/-- Product-law lower bound for any increasing family of observed gap sets. -/
theorem lower_of_pit (h : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    (E : Finset Nat.Primes → Prop) (hE : Monotone E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, eventMass weight s E - ε < fraction X (fun p => E (hits s p)) := by
  classical
  have hl := event_lower (countingAverage h) s E hE hε
  filter_upwards [hl] with X hx
  exact hx.trans_eq (ordinary_eq X (fun p => E (hits s p)))

/-- Product-law upper bound for any decreasing family of observed gap sets. -/
theorem upper_of_pit (h : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    (E : Finset Nat.Primes → Prop) (hE : Antitone E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, fraction X (fun p => E (hits s p)) < eventMass weight s E + ε := by
  classical
  have hl := lower_of_pit h s (fun t => ¬ E t) (fun _ _ hab he => fun hh => he (hE hab hh)) hε
  filter_upwards [hl,Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X hx hX
  have hc := fraction_compl X (by rwa [Nat.primesLE_card_eq_primeCounting]) (fun p => E (hits s p))
  have hm := complement_mass s E
  linarith

/-- Upper bound for a deficit at most D by the product-law probability
of fewer than D retained lengths. -/
theorem deficit_upper_of_pit (h : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, fraction X (fun p => deficit p ≤ D) <
      eventMass weight s (fun t => t.card < D) + ε := by
  classical
  have hl := deficit_lower (countingAverage h) s D hε
  filter_upwards [hl,Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X hx hX
  have hc := fraction_compl X (by rwa [Nat.primesLE_card_eq_primeCounting]) (fun p => D+1 ≤ deficit p)
  have hm := complement_mass s (fun t => D ≤ t.card)
  change _ < ordinary X (fun p => if D+1 ≤ deficit p then 1 else 0) at hx
  rw [ordinary_eq] at hx
  simp only [not_le] at hm hc
  simp only [Nat.lt_succ_iff] at hc
  linarith

#print axioms lower_of_pit
#print axioms upper_of_pit
#print axioms deficit_upper_of_pit

end
end Erdos478.GapSieve
