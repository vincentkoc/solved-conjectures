import Erdos478SharpLocalImage
import Erdos478FirstCollisionLaw

/-! # Density-one sharpness at growing factorial window spans -/

namespace Erdos478.LocalSpacing
open Filter Topology Finset GapSieve FirstCollision GapDensity
open scoped Classical
noncomputable section

private theorem missing_windows {K B X : ℕ} (P : ℕ → Prop)
    (h : ∀ p≥B, p.Prime → ¬P p → NoShort p K) :
    fraction X (fun p => ¬P p)≤(B:ℝ)/(Nat.primesLE X).card+fraction X (fun p => NoShort p K) := by
  classical
  let S := Nat.primesLE X
  have sub : S.filter (fun p => ¬P p) ⊆ range B ∪ S.filter (fun p => NoShort p K) := by
    intro p hp
    obtain ⟨pm,no⟩ := mem_filter.mp hp
    by_cases b : p<B
    · exact mem_union_left _ (mem_range.mpr b)
    · exact mem_union_right _ (mem_filter.mpr ⟨pm,h p (le_of_not_gt b) (Nat.mem_primesLE.mp pm).2 no⟩)
  have count := (card_le_card sub).trans (card_union_le ..)
  rw [card_range] at count
  unfold fraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  convert! count using 1
  congr!

/-- Every diverging choice of span that meets the resultant bound eventually
has sharp minimum image size at a density-one set of rational primes. -/
theorem sharp_density_of_pit (pit : DegreeOnePrimeIdealTheorem) (H : ℕ → ℕ)
    (hg : Tendsto H atTop atTop) (hc : ∀ᶠ p : ℕ in atTop, (H p+2)^(H p^2)<p) :
    Tendsto (fun X => fraction X (fun p => SharpSpan p (H p))) atTop (𝓝 1) := by
  classical
  let P (p : ℕ) := SharpSpan p (H p)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have half : 0<ε/2 := by linarith
  obtain ⟨K,hK⟩ := ((survival_zero pit).eventually_lt_const half).exists
  obtain ⟨B,hB⟩ := eventually_atTop.mp ((hg.eventually_ge_atTop K).and hc)
  have rare (p : ℕ) (pb : B≤p) (hp : p.Prime) (no : ¬P p) : NoShort p K := by
    intro k pos le hit
    obtain ⟨i,hi,hj,rep⟩ := hit
    have lo := (mem_Ico.mp hi).1
    have hi' := (mem_Ico.mp hj).2
    obtain ⟨len,cut⟩ := hB p pb
    exact no ((sharp_iff_pair hp cut).mpr ⟨i,i+k,lo,by omega,hi',by omega,rep⟩)
  have small : Tendsto (fun X : ℕ => (B:ℝ)/(Nat.primesLE X).card) atTop (𝓝 0) := by
    simp only [Nat.primesLE_card_eq_primeCounting]
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting)
  filter_upwards [small.eventually_lt_const half,(survival_limit pit K).eventually_lt_const hK,
    Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X hsmall hrare hpos
  have pos : 0<(Nat.primesLE X).card := by rwa [Nat.primesLE_card_eq_primeCounting]
  have miss := missing_windows (X:=X) P rare
  have all : fraction X P+fraction X (fun p => ¬P p)=1 := by
    rw [fraction,fraction,← add_div,← Nat.cast_add,card_filter_add_card_filter_not,div_self (by exact_mod_cast pos.ne')]
  have nonneg : 0≤fraction X (fun p => ¬P p) := by unfold fraction; positivity
  change dist (fraction X P) 1<ε
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

#print axioms sharp_density_of_pit
end
end Erdos478.LocalSpacing
