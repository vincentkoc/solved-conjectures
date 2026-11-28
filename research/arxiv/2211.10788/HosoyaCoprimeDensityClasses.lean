import LucasFibonacciExactGcdDensities
import HosoyaExactGcdDensityApproximation
import HosoyaExactGcdClasses

/-! Density consequences for the prime-value index sieve. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

/-- Exactly nine of the twelve classes have positive density of coprime indices. -/
theorem coprime_density_mod_twelve (a : ℕ) :
    ∃ δ : ℝ, Tendsto (sampleFreq (gcdFiber 12 a 1)) atTop (𝓝 δ) ∧
      (0 < δ ↔ a%12 ≠ 3 ∧ a%12 ≠ 4 ∧ a%12 ≠ 10) := by
  obtain ⟨δ,lim,pos,_⟩ := exact_gcd_density_decision (by decide : 0<12) (by decide : 0<1) a
  refine ⟨δ,lim,pos.trans ((exactGcdTest_iff (by decide) (by decide) a).trans ?_)⟩
  obtain ⟨bound,realize⟩ := sharp_mod_twelve_minimum a
  constructor
  · rintro ⟨n,_,cl,eq⟩
    have dv := bound n cl
    rw [eq,Nat.dvd_one] at dv
    unfold modTwelveMinimum at dv
    split at dv <;> simp_all
  · rintro ⟨a₃,a₄,a₁₀⟩
    obtain ⟨n,big,cl,hit⟩ := realize 0
    exact ⟨n,big,cl,by simpa [modTwelveMinimum,a₃,a₄,a₁₀] using hit⟩

private def pass168 (n : ℕ) : Prop := fastResidueGcd 168 (n%168)=1
private instance (n : ℕ) : Decidable (pass168 n) := by unfold pass168; infer_instance

private lemma pass168_counts (X : ℕ) : sample (fun n => n.Coprime (lucasFibonacciSum n)) X +
    sample (gcdFiber 1 0 19) X ≤ sample pass168 X := by
  let A := (Icc 1 X).filter (fun n => n.Coprime (lucasFibonacciSum n))
  let B := (Icc 1 X).filter (gcdFiber 1 0 19)
  have ret : 168 ∣ Nat.fib 168 := by
    rw [←show (Nat.fastFibAux 168).1=Nat.fib 168 by simp [Nat.fastFibAux_eq]]
    decide +kernel
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro n ha hb
    have eq₁ : n.gcd (lucasFibonacciSum n)=1 := (mem_filter.mp ha).2
    have eq₂ := (mem_filter.mp hb).2.2
    omega
  have sub : A ∪ B ⊆ (Icc 1 X).filter pass168 := by
    intro n hn
    have test : pass168 n ↔ (168:ℕ).gcd (n.gcd (lucasFibonacciSum n))=1 := by
      rw [pass168,fastResidueGcd_eq,residueGcd_mod ret]
    rcases mem_union.mp hn with h|h
    · obtain ⟨bounds,cop⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨bounds,test.mpr (by rw [show n.gcd (lucasFibonacciSum n)=1 from cop]; decide)⟩
    · obtain ⟨bounds,_,eq⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨bounds,test.mpr (by rw [eq]; decide)⟩
  change A.card+B.card ≤ _
  rw [←card_union_of_disjoint dis]
  exact card_le_card sub

/-- The natural density of indices coprime to their upper value lies strictly between
two thirds and 31/42. The exact gcd-19 fiber occupies positive mass inside the mod-168 sieve. -/
theorem index_coprime_density_strict :
    ∃ δ : ℝ, 2/3 < δ ∧ δ < 31/42 ∧
      Tendsto (sampleFreq (fun n => n.Coprime (lucasFibonacciSum n))) atTop (𝓝 δ) := by
  obtain ⟨δ,low,_,lim⟩ := index_coprime_density
  obtain ⟨η,l₁₉,pos,_⟩ := exact_gcd_density_decision (by decide : 0<1) (by decide : 0<19) 0
  have hit : (228:ℕ).gcd (lucasFibonacciSum 228)=19 := by
    have h : fastResidueGcd 228 228=19 := by decide +kernel
    simpa [fastResidueGcd_eq,residueGcd] using h
  have hp : 0 < η := pos.mpr ((exactGcdTest_iff (by decide) (by decide) 0).mpr
    ⟨228,by decide,Nat.modEq_one,hit⟩)
  have per : Function.Periodic pass168 168 := by intro n; simp [pass168]
  have ml : periodMean pass168 168=31/42 := by
    have count : Nat.count pass168 168=124 := by decide +kernel
    norm_num [periodMean,count]
  have le : δ+η ≤ periodMean pass168 168 := by
    apply le_of_tendsto_of_tendsto (lim.add l₁₉) (periodic_freq_tendsto (by decide) per)
    apply Filter.Eventually.of_forall
    intro X
    change _/(_ : ℝ)+_/(_ : ℝ) ≤ _/(_ : ℝ)
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
    exact_mod_cast pass168_counts X
  exact ⟨δ,low,by linarith,lim⟩

#print axioms coprime_density_mod_twelve
#print axioms index_coprime_density_strict

end Arxiv.«2211.10788».IndexDivisors
