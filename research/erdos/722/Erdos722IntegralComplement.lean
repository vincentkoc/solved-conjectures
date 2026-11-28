import Erdos722SubsetIncidence

/-!
# Complement inversion at the square inclusion matrix

When the ground set has size k+r, a k-block is the complement of an r-set.
Alternating the normalized incidence sums over subsets of its complement
gives integral block weights for every admissible r-vector.
-/

namespace Erdos722.IntegralDesign
open Finset
variable {α : Type*} [DecidableEq α]

theorem alternating_subsets (T : Finset α) :
    (∑ I∈T.powerset, (-1:ℤ)^I.card)=if T=∅ then 1 else 0 := by
  have h := (prod_one_add (f:=fun _ : α => (-1:ℤ)) T).symm
  by_cases he : T=∅
  · simp [he]
  · have hn := (card_pos.mpr (nonempty_iff_ne_empty.mpr he)).ne'
    simpa [prod_const,he,hn] using h

theorem subset_diff (I B A : Finset α) :
    I⊆B\A ↔ I⊆B ∧ Disjoint I A := by
  constructor
  · intro h
    exact ⟨h.trans sdiff_subset,disjoint_left.mpr (fun _ hx ha => (mem_sdiff.mp (h hx)).2 ha)⟩
  · intro h x hx
    exact mem_sdiff.mpr ⟨h.1 hx,fun ha => disjoint_left.mp h.2 hx ha⟩

private theorem complement_count {V A I : Finset α} {r k : ℕ} (hv : V.card=k+r) (hrk : r≤k)
    (hV : I⊆V) (hi : I.card≤r) (hA : A∈V.powersetCard r) (ha : Disjoint I A) :
    #(((V.powersetCard k).filter (A⊆·)).filter (Disjoint I))=(k-I.card).choose (r-I.card) := by
  have hAv := (mem_powersetCard.mp hA).1
  have hAr := (mem_powersetCard.mp hA).2
  have sets : ((V.powersetCard k).filter (A⊆·)).filter (Disjoint I)=
      ((V\I).powersetCard k).filter (A⊆·) := by
    ext B
    simp only [mem_filter,mem_powersetCard,subset_diff,disjoint_comm (a:=B) (b:=I)]
    tauto
  rw [sets,card_filter_powersetCard_subset A (V\I) k ((subset_diff ..).mpr ⟨hAv,ha.symm⟩)
    (hAr ▸ hrk),card_sdiff_of_subset hV,hAr,hv]
  rw [show k+r-I.card-r=k-I.card by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

private theorem cancellation {V A S : Finset α} {r : ℕ} (hA : A∈V.powersetCard r)
    (hS : S∈V.powersetCard r) (y : Finset α → ℤ) :
    (∑ I∈V.powerset.filter (fun I => I.card≤r),
      if Disjoint I A ∧ I⊆S then (-1:ℤ)^I.card*y S else 0) =
      if S=A then y S else 0 := by
  have hs := mem_powersetCard.mp hS
  have he : (V.powerset.filter (fun I => I.card≤r)).filter (fun I => Disjoint I A ∧ I⊆S)=(S\A).powerset := by
    ext I
    simp only [mem_filter,mem_powerset,subset_diff]
    refine ⟨fun h => ⟨h.2.2,h.2.1⟩,fun h => ⟨⟨h.1.trans hs.1,(card_le_card h.1).trans_eq hs.2⟩,h.2,h.1⟩⟩
  have zero : S\A=∅ ↔ S=A := by
    rw [sdiff_eq_empty_iff_subset]
    exact ⟨fun h => eq_of_subset_of_card_le h (by rw [hs.2,(mem_powersetCard.mp hA).2]),fun h => h.le⟩
  rw [← sum_filter,he,← sum_mul,alternating_subsets]
  by_cases h : S=A <;> simp [zero,h]

/-- Each admissible integer vector on the r-subsets of a (k+r)-set is the
incidence vector of integer weights on its k-subsets. -/
theorem boundary_weights {V : Finset α} {r k : ℕ} (hv : V.card=k+r) (hrk : r≤k)
    {y : Finset α → ℤ} (hy : Admissible V r k y) :
    ∃ w, Represents V r k y w := by
  classical
  let T := V.powerset.filter (fun I => I.card≤r)
  have div (I : Finset α) (hI:I∈T) := hy I (mem_powerset.mp (mem_filter.mp hI).1) (mem_filter.mp hI).2
  let d (I : Finset α) := if h : I∈T then (div I h).choose else 0
  have quotient_spec (I : Finset α) (hI:I∈T) :
      incidence V r y I = (((k-I.card).choose (r-I.card):ℕ):ℤ)*d I := by
    simpa [d,hI] using (div I hI).choose_spec
  let w (B : Finset α) := ∑ I∈T, if Disjoint I B then (-1:ℤ)^I.card*d I else 0
  refine ⟨w,?_⟩
  intro A hA
  let blocks := (V.powersetCard k).filter (A⊆·)
  have count (I) (hI:I∈T) :
      (∑ B∈blocks, if Disjoint I B then (-1:ℤ)^I.card*d I else 0) =
        if Disjoint I A then (-1:ℤ)^I.card*incidence V r y I else 0 := by
    by_cases ha : Disjoint I A
    · rw [if_pos ha,← sum_filter,sum_const,nsmul_eq_mul,quotient_spec I hI]
      rw [show #(blocks.filter (Disjoint I))=_ from complement_count hv hrk
        (mem_powerset.mp (mem_filter.mp hI).1) (mem_filter.mp hI).2 hA ha]
      ring
    · rw [if_neg ha]
      exact sum_eq_zero fun B hB => if_neg (fun h => ha (h.mono_right (mem_filter.mp hB).2))
  calc
    incidence V k w A = ∑ I∈T, ∑ B∈blocks, if Disjoint I B then (-1:ℤ)^I.card*d I else 0 := sum_comm
    _ = ∑ I∈T, if Disjoint I A then (-1:ℤ)^I.card*incidence V r y I else 0 := sum_congr rfl count
    _ = ∑ I∈T, ∑ S∈V.powersetCard r, if Disjoint I A ∧ I⊆S then (-1:ℤ)^I.card*y S else 0 := by
      apply sum_congr rfl
      intro I _
      by_cases h : Disjoint I A <;> simp [h,incidence,mul_sum,sum_filter,mul_ite]
    _ = ∑ S∈V.powersetCard r, ∑ I∈T, if Disjoint I A ∧ I⊆S then (-1:ℤ)^I.card*y S else 0 := sum_comm
    _ = ∑ S∈V.powersetCard r, if S=A then y S else 0 := sum_congr rfl fun _ hS => cancellation hA hS y
    _ = y A := by simp [hA]

#print axioms boundary_weights
end Erdos722.IntegralDesign
