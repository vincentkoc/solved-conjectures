import Erdos478ConditionalGapAction
import Mathlib.Data.Nat.Choose.Sum

/-! # Stochastic domination of the set of collision-bearing lengths -/

namespace Erdos478.ConditionalGaps
open Finset Polynomial FrobeniusCounts BinaryGap
noncomputable section
open scoped Classical

/-- Expectation of a score under independent fair inclusion of each member. -/
def fair {ι : Type*} (s : Finset ι) (w : Finset ι → ℝ) := (∑ u∈s.powerset, w u)/2^s.card

theorem fair_insert {ι : Type*} [DecidableEq ι] {s : Finset ι} {i : ι} (hi : i∉s) (w : Finset ι → ℝ) :
    fair (insert i s) w=(fair s w+fair s (fun u => w (insert i u)))/2 := by
  rw [fair,sum_powerset_insert hi,card_insert_of_notMem hi,pow_succ]
  unfold fair
  ring

variable (K : Type*) [Field K] [Algebra ℚ K]
def hits (s : Finset Nat.Primes) (g : Aut K) := s.filter (fun i => 0<count K i g)

private theorem hits_stable {s : Finset Nat.Primes} (h : kernel K s) (g : Aut K) :
    hits K s (h.val*g)=hits K s g := by
  unfold hits
  exact filter_congr fun i hi => by rw [count_stable K h g hi]

variable [FiniteDimensional ℚ K] [Normal ℚ K]

/-- The inequality holds simultaneously for every increasing real score,
without any independence assumption on the root counts. -/
theorem dominates (s : Finset Nat.Primes) (good : ∀ i∈s, broad i.val ∧ 3 < i.val)
    (split : ∀ i∈s, ((rationalGap i.val).map (algebraMap ℚ K)).Splits)
    (f : Finset Nat.Primes → ℝ) (inc : Monotone f) :
    fair s f≤uniform (Aut K) (fun g => f (hits K s g)) := by
  classical
  induction s using Finset.induction_on_max_value (fun i : Nat.Primes => i.val) generalizing f with
  | empty =>
    simp [hits,fair,uniform,Fintype.card_ne_zero]
  | insert l s hl top ih =>
    have small (i) (hi : i∈s) : i.val<l.val := (top i hi).lt_of_ne
      (fun he => hl (Subtype.ext he ▸ hi))
    have gs (i) (hi : i∈s) := good i (mem_insert_of_mem hi)
    have ss (i) (hi : i∈s) := split i (mem_insert_of_mem hi)
    let E (g : Aut K) := f (hits K s g)
    let U (g : Aut K) := f (insert l (hits K s g))
    have stable (n : kernel K s) (g : Aut K) : (U-E) (n.val*g)=(U-E) g := by
      simp only [Pi.sub_apply,E,U,hits_stable K n g]
    have half := gap_conditional_half K s l (good l (mem_insert_self ..)).1 (good l (mem_insert_self ..)).2
      small split (U-E) (fun g => sub_nonneg.mpr (inc (subset_insert _ _))) stable
    let gain (g : Aut K) : ℝ := if 0<count K l g then (U-E) g else 0
    change uniform (Aut K) (U-E)≤2*uniform (Aut K) gain at half
    rw [map_sub] at half
    have eq : (fun g => f (hits K (insert l s) g))=E+gain := by
      funext g
      by_cases h : 0<count K l g <;> simp [E,U,gain,hits,filter_insert,h]
    have low : fair s f≤uniform (Aut K) E := ih gs ss f inc
    have high : fair s (fun u => f (insert l u))≤uniform (Aut K) U :=
      ih gs ss _ (fun _ _ h => inc (insert_subset_insert _ h))
    rw [fair_insert hl,eq,map_add]
    linarith

#print axioms fair
#print axioms fair_insert
#print axioms hits
#print axioms dominates
end
end Erdos478.ConditionalGaps
