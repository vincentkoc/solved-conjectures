import Erdos478GapSplittingTest

/-!
# Exact prime averages for finite splitting patterns

Each complete-splitting condition has mean equal to the inverse degree
of its splitting field. Inclusion-exclusion then distinguishes every
prescribed pattern of complete and incomplete gap splitting.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset Filter Topology RootMoments
open scoped Classical
noncomputable section

def event (P : ℕ → Prop) (p : ℕ) : ℝ := if P p then 1 else 0

theorem split_mean (A : PrimeAverage) (f : ℤ[X]) (hm : f.Monic) (hn : 0<f.natDegree)
    (hs : (f.map (Int.castRingHom ℚ)).Separable) :
    Tendsto (fun X => A.avg X (indicator f)) atTop (𝓝 (Module.finrank ℚ (SplitField f):ℝ)⁻¹) := by
  obtain ⟨h,hh,hir,hd,B,hB⟩ := separating_factor f hm hn hs
  let d : ℝ := h.natDegree
  have hdpos : d≠0 := by
    dsimp [d]; rw [hd]; exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=SplitField f)).ne'
  have hc := A.finite_change (a:=indicator f) (b:=d⁻¹ • RootMoments.roots h) B (by
    intro p hp hpr
    simp only [Pi.smul_apply,smul_eq_mul,hB p hp hpr]
    change indicator f p=d⁻¹*(d*indicator f p)
    rw [← mul_assoc,inv_mul_cancel₀ hdpos,one_mul])
  have hmean := (first_mean A h hh hir).const_mul d⁻¹
  rw [mul_one] at hmean
  have h' : Tendsto (fun X => A.avg X (d⁻¹ • RootMoments.roots h)) atTop (𝓝 d⁻¹) := by
    simpa only [map_smul,smul_eq_mul] using hmean
  simpa only [sub_add_cancel,zero_add,d,hd] using hc.add h'

def splitDensity (m : ℕ) (S : Finset ℕ) : ℝ :=
  (Module.finrank ℚ (SplitField (test m S)) : ℝ)⁻¹

theorem complete_mean (A : PrimeAverage) {m : ℕ} (hm : 0<m) {S : Finset ℕ}
    (hS : ∀ k∈S, 0<k) :
    Tendsto (fun X => A.avg X (event (complete m S))) atTop (𝓝 (splitDensity m S)) := by
  obtain ⟨hmon,hn,hsep⟩ := test_properties hm hS
  have h := A.finite_change (a:=event (complete m S)) (b:=indicator (test m S)) m (by
    intro p hp hpr
    let : Fact p.Prime := ⟨hpr⟩
    simp only [event,indicator,test_iff hm hp hS])
  simpa only [sub_add_cancel,zero_add,splitDensity] using h.add (split_mean A _ hmon hn hsep)

def pattern (m : ℕ) (S T : Finset ℕ) (p : ℕ) : Prop :=
  complete m S p ∧ ∀ k∈T, ¬((gapPoly k).map (Int.castRingHom (ZMod p))).Splits

def patternDensity (m : ℕ) (S T : Finset ℕ) : ℝ :=
  ∑ U ∈ T.powerset, (-1:ℝ)^U.card * splitDensity m (S∪U)

private theorem pattern_insert (m k : ℕ) (S T : Finset ℕ) :
    event (pattern m S (insert k T)) =
      event (pattern m S T) - event (pattern m (insert k S) T) := by
  funext p
  let Q := ((gapPoly k).map (Int.castRingHom (ZMod p))).Splits
  have h₁ : pattern m S (insert k T) p ↔ pattern m S T p ∧ ¬Q := by
    simp only [pattern,forall_mem_insert,Q]
    tauto
  have h₂ : pattern m (insert k S) T p ↔ pattern m S T p ∧ Q := by
    simp only [pattern,complete,forall_mem_insert,Q]
    tauto
  simp only [Pi.sub_apply,event,h₁,h₂]
  by_cases hP : pattern m S T p <;> by_cases hQ : Q <;> simp [hP,hQ]

private theorem density_insert {m k : ℕ} {S T : Finset ℕ} (hk : k∉T) :
    patternDensity m S (insert k T)=patternDensity m S T-patternDensity m (insert k S) T := by
  simp only [patternDensity,sum_powerset_insert hk,sub_eq_add_neg,← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro U hU
  have hn : k∉U := fun h => hk ((mem_powerset.mp hU) h)
  rw [card_insert_of_notMem hn,pow_succ]
  simp [Finset.union_insert,Finset.insert_union]

/-- The joint law for prescribed fully split and non-fully split gap lengths. -/
theorem pattern_mean (A : PrimeAverage) {m : ℕ} (hm : 0<m) (S T : Finset ℕ)
    (hS : ∀ k∈S, 0<k) (hT : ∀ k∈T, 0<k) :
    Tendsto (fun X => A.avg X (event (pattern m S T))) atTop (𝓝 (patternDensity m S T)) := by
  induction T using Finset.induction_on generalizing S with
  | empty =>
    rw [show pattern m S ∅=complete m S by funext p; simp [pattern]]
    simpa [patternDensity] using complete_mean A hm hS
  | insert k T hk ih =>
    have ht := fun j (hj:j∈T) => hT j (mem_insert_of_mem hj)
    have hs' : ∀ j∈insert k S, 0<j := by
      intro j hj
      rcases mem_insert.mp hj with rfl|hj
      · exact hT _ (mem_insert_self ..)
      · exact hS _ hj
    rw [density_insert hk,pattern_insert]
    simpa only [map_sub] using (ih S hS ht).sub (ih (insert k S) hs' ht)

#print axioms split_mean
#print axioms complete_mean
#print axioms pattern_mean
end
end Erdos478.SplittingDensity
