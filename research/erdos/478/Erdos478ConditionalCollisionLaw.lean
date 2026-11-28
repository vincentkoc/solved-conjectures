import Erdos478GapObservableLaw
import Erdos478SieveProportions

/-! # Collision probabilities conditional on an arbitrary earlier count event -/

namespace Erdos478.ConditionalGaps
open Finset Polynomial FrobeniusCounts BinaryGap GapDensity RootMoments SplittingDensity Filter Topology
open scoped Classical
noncomputable section

/-- For any test on the actual counts at the smaller primes, the two natural
densities exist. Requiring a collision at the new length preserves at least
half the initial density. Zero-density conditions are allowed. -/
theorem conditional_of_pit (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes) (l : Nat.Primes)
    (hb : broad l.val) (h3 : 3 < l.val) (small : ∀ i∈s, i.val<l.val) (E : (s → ℕ) → Prop) :
    ∃ d e : ℝ, d≤2*e ∧
      Tendsto (fun X => GapSieve.fraction X (fun p => E (fun i => (endpoints i.val.val p).card))) atTop (𝓝 d) ∧
      Tendsto (fun X => GapSieve.fraction X (fun p => E (fun i => (endpoints i.val.val p).card) ∧
        GapSieve.HasGap p l.val)) atTop (𝓝 e) := by
  classical
  let T := insert l s
  let K := CommonField T
  let : Normal ℚ K := SplittingField.instNormal (familyPoly T)
  let old (a : T → ℕ) (i : s) := a ⟨i.val,mem_insert_of_mem i.prop⟩
  let j : T := ⟨l,mem_insert_self ..⟩
  let W (a : T → ℕ) : ℝ := if E (old a) then 1 else 0
  let V (a : T → ℕ) : ℝ := if 0<a j then W a else 0
  let w (g : Aut K) : ℝ := W (fun i => count K i.val g)
  let v (g : Aut K) : ℝ := V (fun i => count K i.val g)
  refine ⟨uniform (Aut K) w,uniform (Aut K) v,?_,?_,?_⟩
  · apply gap_conditional_half K s l hb h3 small (fun i hi => common_splits hi) w
    · intro g
      simp only [w,W]
      split_ifs <;> norm_num
    · intro n g
      have eq : old (fun i => count K i.val (n.val*g))=old (fun i => count K i.val g) :=
        funext fun i => count_stable K n g i.prop
      simp only [w,W,eq]
  · apply (endpoint_mean (countingAverage pit) T W).congr
    intro X
    exact GapSieve.ordinary_eq X _
  · apply (endpoint_mean (countingAverage pit) T V).congr
    intro X
    rw [← GapSieve.ordinary_eq]
    apply congrArg (ordinary X)
    funext p
    simp only [V,W,old,j,hasGap_iff]
    split_ifs <;> tauto

/-- Every real weight determined by the smaller endpoint counts has exact
first and second moments at the new length, including signed weights. -/
theorem conditional_endpoint_moments (A : PrimeAverage) (s : Finset Nat.Primes) (l : Nat.Primes)
    (hb : broad l.val) (h3 : 3 < l.val) (small : ∀ i∈s, i.val<l.val) (W : (s → ℕ) → ℝ) :
    ∃ d : ℝ,
      Tendsto (fun X => A.avg X (fun p => W (fun i => (endpoints i.val.val p).card))) atTop (𝓝 d) ∧
      Tendsto (fun X => A.avg X (fun p => W (fun i => (endpoints i.val.val p).card)*(endpoints l.val p).card)) atTop (𝓝 d) ∧
      Tendsto (fun X => A.avg X (fun p => W (fun i => (endpoints i.val.val p).card)*((endpoints l.val p).card : ℝ)^2)) atTop (𝓝 (2*d)) := by
  classical
  let T := insert l s
  let K := CommonField T
  let : Normal ℚ K := SplittingField.instNormal (familyPoly T)
  let w (a : T → ℕ) := W (fun i => a ⟨i.val,mem_insert_of_mem i.prop⟩)
  let y (g : Aut K) := w (fun i => count K i.val g)
  let j : T := ⟨l,mem_insert_self ..⟩
  have hc : Fintype.card (Roots K l)=l.val := gap_card K l.prop (common_splits (s:=T) j.prop)
  let : Nontrivial (Roots K l) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have st (n : kernel K s) (g : Aut K) : y (n.val*g)=y g :=
    congrArg W (funext fun i => count_stable K n g i.prop)
  obtain ⟨one,two⟩ := conditional_moments (kernel K s)
    (kernel_pairs K s l hb h3 small (fun i hi => common_splits hi)) y st
  refine ⟨uniform (Aut K) y,endpoint_mean A T w,?_,?_⟩
  · rw [← one]
    exact endpoint_mean A T (fun a => w a*(a j:ℝ))
  · rw [← two]
    exact endpoint_mean A T (fun a => w a*(a j:ℝ)^2)

#print axioms conditional_endpoint_moments
#print axioms conditional_of_pit
end
end Erdos478.ConditionalGaps
