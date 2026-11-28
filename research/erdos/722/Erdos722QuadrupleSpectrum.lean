import Erdos722FourfoldRule
import Erdos722HananiThree
import Erdos722HananiFour

/-!
# Hanani's spectrum for Steiner quadruple systems

The fourfold construction fills in the last recurrence in the notebook's
proof of Hanani's spectrum. In particular the divisibility hypotheses of
Erdős 722 suffice at rank three and block size four for every order at
least four.
-/

namespace Erdos722.Fourfold
open HananiTwelve

private def coordinates (k : ℕ) : Point k ≃ Bit ⊕ (Bit × Bit × Label k) where
  toFun
    | .stem s => .inl s
    | .pt h i x => .inr (h,i,x)
  invFun
    | .inl s => .stem s
    | .inr (h,i,x) => .pt h i x
  left_inv := by intro a; cases a <;> rfl
  right_inv := by rintro (_|⟨h,i,x⟩) <;> rfl

/-- From a quadruple system on `2k+4` points construct one on `8k+10` points.
The four copies share two stem points and have disjoint ordinary columns. -/
theorem fourfold (k : ℕ) (h : HasSQS (2*k+4)) : HasSQS (8*k+10) := by
  classical
  obtain ⟨B,hB⟩ := h
  let e : Fin (2*k+4) ≃ Bit ⊕ Label k := Fintype.equivOfCardEq (by simp [Label,Bit]; omega)
  let Q := HananiThree.sourceRule (StemInflation.relabel hB e)
  let f : Point k ≃ Fin (8*k+10) := Fintype.equivOfCardEq (by
    rw [Fintype.card_congr (coordinates k)]
    simp [Label,Bit]; omega)
  exact ⟨_,StemInflation.relabel (rule Q).isBlockDesign f⟩

/-- Every order congruent to two or four modulo six admits a Steiner
quadruple system, including the vacuous two-point design. -/
theorem admissible_quadruples (n : ℕ) (h : n%6=2 ∨ n%6=4) : HasSQS n := by
  apply HananiThree.spectrum_of_fourfold _ n h
  intro m hm hr hB
  let k := (m-4)/2
  have hn : m=2*k+4 := by dsimp [k]; omega
  have hq := fourfold k (hn ▸ hB)
  convert hq using 1
  omega

/-- Exact spectrum for the upstream predicate, including its vacuous designs. -/
theorem quadruple_spectrum (n : ℕ) : HasSQS n ↔ n ≤ 2 ∨ n%6=2 ∨ n%6=4 := by
  constructor
  · rintro ⟨B,hB⟩
    by_cases hn : 4 ≤ n
    · exact Or.inr (residues_of_divisibility hn (fun i hi =>
        Quartet.design_divisibility hB (by omega) hi.le))
    · left
      by_contra! h
      obtain rfl : n=3 := by omega
      have hd := Quartet.design_divisibility (i := 2) hB (by decide) (by decide)
      exact (by decide : ¬ (4-2).choose (3-2) ∣ (3-2).choose (3-2)) hd
  · rintro (hn|hr)
    · refine ⟨∅,fun _ he => (Finset.notMem_empty _ he).elim,?_⟩
      intro T ht
      have he := Finset.card_le_univ T
      simp only [Fintype.card_fin] at he
      omega
    · exact admissible_quadruples n hr

/-- At `r=3`, `k=4`, the pinned binomial divisibility assumptions suffice
at every order at least four. -/
theorem quadruples_of_divisibility (n : ℕ) (hn : 4 ≤ n)
    (h : ∀ i < 3, (4-i).choose (3-i) ∣ (n-i).choose (3-i)) :
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 4 :=
  admissible_quadruples n (residues_of_divisibility hn h)

/-- The exact eventual conclusion and hypotheses of Erdős 722 at `r=3`, `k=4`. -/
theorem eventually_quadruples :
    ∀ᶠ n : ℕ in Filter.atTop, (∀ i < 3, (4-i).choose (3-i) ∣ (n-i).choose (3-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 4 := by
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn h
  exact quadruples_of_divisibility n hn h

#print axioms fourfold
#print axioms admissible_quadruples
#print axioms quadruple_spectrum
#print axioms quadruples_of_divisibility
#print axioms eventually_quadruples

end Erdos722.Fourfold
