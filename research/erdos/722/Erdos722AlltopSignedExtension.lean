import Erdos722ComplementIncidence

/-! # Alltop's extension by complementation for signed design weights

At even strength a point and the complementary blocks extend a design on
2k+1 points by one rank, with the index and the block weights preserved.
-/

namespace Erdos722.ComplementExtension
open Finset IntegralDesign
variable {α : Type*} [DecidableEq α]

def extend (o : α) (V : Finset α) (w : Finset α → ℤ) (B : Finset α) : ℤ :=
  if o∈B then w (B.erase o) else w (V\B)

theorem complement_incidence {V A : Finset α} {j k : ℕ} (hv : V.card=j+k) (hA : A⊆V)
    (w : Finset α → ℤ) :
    incidence V j (fun B => w (V\B)) A=avoiding V k w A := by
  classical
  apply sum_nbij' (fun B => V\B) (fun B => V\B) _ _ _ _ (fun _ _ => rfl)
  · intro B h
    obtain ⟨hb,hAB⟩ := mem_filter.mp h
    obtain ⟨hBV,hb⟩ := mem_powersetCard.mp hb
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset,by rw [card_sdiff_of_subset hBV,hv,hb]; omega⟩,
      disjoint_left.mpr (fun _ ha hh => (mem_sdiff.mp hh).2 (hAB ha))⟩
  · intro B h
    obtain ⟨hb,hAB⟩ := mem_filter.mp h
    obtain ⟨hBV,hb⟩ := mem_powersetCard.mp hb
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset,by rw [card_sdiff_of_subset hBV,hv,hb]; omega⟩,
      subset_sdiff.mpr ⟨hA,hAB⟩⟩
  · exact fun _ h => Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp (mem_filter.mp h).1).1
  · exact fun _ h => Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp (mem_filter.mp h).1).1

theorem extension_row {o : α} {V : Finset α} (ho : o∉V) {k : ℕ} (w : Finset α → ℤ) (I : Finset α) :
    incidence (insert o V) (k+1) (extend o V w) I=
      incidence V (k+1) (fun B => w (V\B)) I + incidence V k w (I.erase o) := by
  rw [incidence_insert ho]
  congr 1
  · exact incidence_congr (fun B hB => if_neg (fun h => ho ((mem_powersetCard.mp hB).1 h))) _
  · apply incidence_congr
    intro B hB
    have no : o∉B := fun h => ho ((mem_powersetCard.mp hB).1 h)
    simp [extend,no]

private theorem extend_zero {o : α} {V : Finset α} (ho : o∉V) {r k : ℕ}
    (hv : V.card=2*k+1) (hrk : r≤k) (even : Even r) {w : Finset α → ℤ}
    (hw : Represents V r k (fun _ => 0) w) :
    Represents (insert o V) (r+1) (k+1) (fun _ => 0) (extend o V w) := by
  intro I hi
  obtain ⟨hin,hc⟩ := mem_powersetCard.mp hi
  rw [extension_row ho]
  by_cases h : o∈I
  · have outside : ¬I⊆V := fun sub => ho (sub h)
    have er : I.erase o⊆V := by
      intro x hx
      exact (mem_insert.mp (hin (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1
    rw [incidence_outside outside,hw _ (mem_powersetCard.mpr ⟨er,by rw [card_erase_of_mem h,hc]; omega⟩),add_zero]
  · have old := (subset_insert_iff_of_notMem h).mp hin
    rw [complement_incidence (k:=k) (by omega) old,erase_eq_of_notMem h,next_row_duality hrk hw hc,hc]
    have odd : Odd (r+1) := even.add_odd odd_one
    rw [odd.neg_one_pow,neg_one_mul,neg_add_cancel]

/-- Integer weights of arbitrary index extend by retaining their values on
the blocks through the new point and assigning them to the opposite blocks. -/
theorem extend_signed {o : α} {V : Finset α} (ho : o∉V) {r k : ℕ}
    (hv : V.card=2*k+1) (hrk : r≤k) (even : Even r) {l : ℤ} {w : Finset α → ℤ}
    (hw : Represents V r k (fun _ => l) w) :
    Represents (insert o V) (r+1) (k+1) (fun _ => l) (extend o V w) := by
  let d : ℤ := (V.card-r).choose (k-r)
  have hd : d≠0 := by
    dsimp [d]
    exact_mod_cast (Nat.choose_pos (show k-r≤V.card-r by omega)).ne'
  have eq : extend o V (center V r k l w)=center (insert o V) (r+1) (k+1) l (extend o V w) := by
    funext B
    by_cases h : o∈B <;> simp [extend,center,h,card_insert_of_notMem ho,Nat.succ_sub_succ_eq_sub]
  have hz := extend_zero ho hv hrk even (center_zero hrk hw)
  rw [eq] at hz
  intro A hA
  obtain ⟨sub,hc⟩ := mem_powersetCard.mp hA
  have e := hz A hA
  rw [incidence_center _ _ _ _ sub (by omega),hc,card_insert_of_notMem ho,Nat.succ_sub_succ_eq_sub,
    Nat.succ_sub_succ_eq_sub] at e
  change d*incidence (insert o V) (k+1) (extend o V w) A-d*l=0 at e
  exact (mul_left_cancel₀ hd) (sub_eq_zero.mp e)

#print axioms extend
#print axioms complement_incidence
#print axioms extension_row
#print axioms extend_signed
end Erdos722.ComplementExtension
