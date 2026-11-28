import Erdos722ReducedLatinRows

/-! # The exact number of labelled Latin cubes on four symbols -/

namespace Erdos722.LatinFillings
open Finset

private instance (q : Table) : Decidable (Latin q) := by
  unfold Latin Function.Injective
  infer_instance
private instance (q : Table) : Decidable (Normal q) := by
  unfold Normal
  infer_instance

/-- The computation explores at most 111 surviving row prefixes at any one depth. -/
private theorem enumeration : (pool 16).length = 64 ∧ (pool 16).Nodup := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 15000000 in
  decide +kernel

private theorem certificates : ∀ s ∈ pool 16, Latin (decodeRows s) ∧ Normal (decodeRows s) ∧
    prefixRows (decodeRows s) 16=s := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 15000000 in
  decide +kernel

/-- Encode the rows of a normalized cube and recover it by digit extraction. -/
def reducedRows : Reduced ≃ {s // s ∈ (pool 16).toFinset} where
  toFun q := ⟨_,List.mem_toFinset.mpr (prefix_mem_pool q (le_refl 16))⟩
  invFun s := ⟨⟨decodeRows s.val,(certificates _ (List.mem_toFinset.mp s.prop)).1⟩,
    (certificates _ (List.mem_toFinset.mp s.prop)).2.1⟩
  left_inv q := Subtype.ext (Subtype.ext (decode_prefix q.val.val))
  right_inv s := Subtype.ext (certificates _ (List.mem_toFinset.mp s.prop)).2.2

theorem reduced_cube_count : Nat.card Reduced = 64 := by
  rw [Nat.card_congr reducedRows,Nat.card_eq_fintype_card,Fintype.card_coe,
    List.toFinset_card_of_nodup enumeration.2,enumeration.1]

theorem latin_cube_count : Nat.card Quasigroup = 55296 := by
  rw [labelled_cube_count,reduced_cube_count]

#print axioms reducedRows
#print axioms reduced_cube_count
#print axioms latin_cube_count

end Erdos722.LatinFillings
