import Erdos722CountCompatibleDoublings
import Erdos722UnlabelledBlockFamilies
import Erdos722PointedDesignProduct

/-!
# Iterated labelled and unlabelled counts on the canonical finite ground set

At each doubling one can recover the immediately preceding system. Forgetting
all labels at the end costs at most the factorial of the final order.
-/

namespace Erdos722.QuadSwitch
open Finset

def blockNumber (v : ℕ) := v.choose 3 / 4

theorem blockNumber_formula (v : ℕ) : blockNumber v = v*(v-1)*(v-2)/24 := by
  rw [blockNumber,Nat.choose_eq_descFactorial_div_factorial,Nat.div_div_eq_div_mul]
  simp [Nat.descFactorial_succ,Nat.factorial_succ,Nat.mul_comm]

noncomputable def labelledCount (v : ℕ) := Nat.card (Systems (Fin v))

private theorem relabel {V W : Type*} [DecidableEq W] (e : V ≃ W) {H : Finset (Finset V)}
    (hH : H.IsBlockDesign 3 4) : (e.finsetCongr.finsetCongr H).IsBlockDesign 3 4 := by
  change (H.map e.finsetCongr.toEmbedding).IsBlockDesign 3 4
  rw [map_eq_image]
  exact PointedProduct.relabel_design e hH

/-- Relabelling preserves the count of canonical systems. -/
theorem systems_card_congr {V W : Type*} (e : V ≃ W) : Nat.card (Systems V) = Nat.card (Systems W) := by
  classical
  apply Nat.card_congr
  apply e.finsetCongr.finsetCongr.subtypeEquiv
  intro H
  refine ⟨relabel e,fun h => ?_⟩
  exact e.finsetCongr.finsetCongr.symm_apply_apply H ▸ relabel e.symm h

theorem double_count (v : ℕ) : labelledCount v * 2^(blockNumber v) ≤ labelledCount (2*v) := by
  classical
  let e : Fin v × Bool ≃ Fin (2*v) := Fintype.equivOfCardEq (by simp [Nat.mul_comm])
  have bound := Nat.card_le_card_of_injective (fun D : CompatibleSystems (Fin v) => D.val) Subtype.val_injective
  rw [all_lifts_count,systems_card_congr e] at bound
  simpa only [labelledCount,blockNumber,Fintype.card_fin] using bound

/-- Number of independently chosen bits over the successive recovered bases. -/
def switchExponent (v m : ℕ) := ∑ j ∈ range m, blockNumber (2^j*v)

theorem iterate_count (v m : ℕ) :
    labelledCount v * 2^(switchExponent v m) ≤ labelledCount (2^m*v) := by
  induction m with
  | zero => simp [switchExponent]
  | succ m ih =>
    have exp : switchExponent v (m+1) = switchExponent v m + blockNumber (2^m*v) := sum_range_succ _ _
    rw [exp,pow_add,← Nat.mul_assoc]
    refine (Nat.mul_le_mul_right _ ih).trans ?_
    have next := double_count (2^m*v)
    rwa [show 2^(m+1)*v = 2*(2^m*v) by rw [pow_succ]; ring]

theorem many_representatives (v m : ℕ) (seed : Nonempty (Systems (Fin v))) :
    ∃ R : Finset (Finset (Finset (Fin (2^m*v)))),
      (∀ D ∈ R, D.IsBlockDesign 3 4) ∧
      (R : Set (Finset (Finset (Fin (2^m*v))))).Pairwise (fun D E => ¬Isomorphic D E) ∧
      labelledCount v * 2^(switchExponent v m) ≤ R.card * (2^m*v).factorial ∧
      2^(switchExponent v m - Nat.clog 2 (2^m*v).factorial) ≤ R.card := by
  classical
  let n := 2^m*v
  let F := (univ : Finset (Finset (Finset (Fin n)))).filter (fun D => D.IsBlockDesign 3 4)
  have hc : F.card = labelledCount n := by
    change _ = Nat.card (Systems (Fin n))
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  obtain ⟨R,sub,pair,bound⟩ := representatives F
  rw [hc,Fintype.card_fin] at bound
  have stronger := (iterate_count v m).trans bound
  have pos : 0 < labelledCount v := Nat.card_pos_iff.mpr ⟨seed,inferInstance⟩
  have le : 2^(switchExponent v m) ≤ labelledCount v * 2^(switchExponent v m) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^(switchExponent v m)) (show 1 ≤ labelledCount v by omega)
  exact ⟨R,fun D h => (mem_filter.mp (sub h)).2,pair,stronger,unlabelled_exponent (le.trans stronger)⟩

#print axioms double_count
#print axioms iterate_count
#print axioms many_representatives
end Erdos722.QuadSwitch
