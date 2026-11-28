import Erdos722SignedIndexSpectrum

/-!
# Orders at most k+r

When the complement of a block has at most r points, inclusion-exclusion
on that complement recovers its weight. For constant demands the local
divisibilities already force the index to be a multiple of the complete
design index, and constant natural weights realize every such index.
-/

namespace Erdos722.IntegralDesign
open Finset
variable {α : Type*} [DecidableEq α]

/-- The incidence sums on subsets of the complement recover a single block weight. -/
theorem isolate_block {V B : Finset α} {k : ℕ} (hB : B∈V.powersetCard k) (w : Finset α → ℤ) :
    (∑ I∈(V\B).powerset, (-1:ℤ)^I.card*incidence V k w I)=w B := by
  have inner (K) (hK:K∈V.powersetCard k) :
      (∑ I∈(V\B).powerset, if I⊆K then (-1:ℤ)^I.card*w K else 0) =
        if K=B then w K else 0 := by
    have he : (V\B).powerset.filter (· ⊆ K)=(K\B).powerset := by
      ext I
      simp only [mem_filter,mem_powerset,subset_diff]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans (mem_powersetCard.mp hK).1,h.2⟩,h.1⟩⟩
    have hz : K\B=∅ ↔ K=B := by
      rw [sdiff_eq_empty_iff_subset]
      exact ⟨fun h => eq_of_subset_of_card_le h (by rw [(mem_powersetCard.mp hB).2,(mem_powersetCard.mp hK).2]),fun h => h.le⟩
    rw [← sum_filter,he,← sum_mul,alternating_subsets]
    by_cases h : K=B <;> simp [hz,h]
  calc
    _ = ∑ I∈(V\B).powerset, ∑ K∈V.powersetCard k, if I⊆K then (-1:ℤ)^I.card*w K else 0 := by
      simp [incidence,mul_sum,sum_filter,mul_ite]
    _ = ∑ K∈V.powersetCard k, ∑ I∈(V\B).powerset, if I⊆K then (-1:ℤ)^I.card*w K else 0 := sum_comm
    _ = ∑ K∈V.powersetCard k, if K=B then w K else 0 := sum_congr rfl inner
    _ = w B := by simp [hB]

theorem multiples_realized (V : Finset α) {r k l : ℕ} (hrk : r≤k)
    (h : (V.card-r).choose (k-r) ∣ l) : Multiplicities V r k l := by
  obtain ⟨d,hd⟩ := h
  refine ⟨fun _ => d,fun A hA => ?_⟩
  obtain ⟨hAv,hc⟩ := mem_powersetCard.mp hA
  rw [sum_const,nsmul_eq_mul,card_filter_powersetCard_subset _ _ _ hAv (hc ▸ hrk),hc,hd]
  rfl

/-- For small orders the complete design already realizes every admissible index. -/
theorem small_order_period (V : Finset α) {r k l : ℕ} (hrk : r≤k) (hkv : k≤V.card)
    (hsmall : V.card≤k+r) :
    Conditions V.card r k l ↔ (V.card-r).choose (k-r) ∣ l := by
  classical
  refine ⟨?_,fun h => conditions_of_multiplicities (hrk.trans hkv) (multiples_realized V hrk h)⟩
  intro H
  let C := (V.card-r).choose (k-r)
  have hy := (admissible_constant V (hrk.trans hkv)).mpr H
  obtain ⟨B,hBv,hBk⟩ := exists_subset_card_eq hkv
  have hB := mem_powersetCard.mpr ⟨hBv,hBk⟩
  let T := (V\B).powerset
  have size (I) (hI:I∈T) : I.card≤r := by
    have he := card_le_card (mem_powerset.mp hI)
    rw [card_sdiff_of_subset hBv,hBk] at he
    omega
  have sub (I) (hI:I∈T) : I⊆V := (mem_powerset.mp hI).trans sdiff_subset
  have div (I) (hI:I∈T) := hy I (sub I hI) (size I hI)
  let d (I : Finset α) := if h : I∈T then (div I h).choose else 0
  have ones (A) (hA:A∈V.powersetCard r) : incidence V k (fun _ => (1:ℤ)) A=(C:ℤ) := by
    obtain ⟨hAv,hc⟩ := mem_powersetCard.mp hA
    rw [constant_incidence _ _ _ _ hAv (hc ▸ hrk),hc,mul_one]
  have scale (I) (hI:I∈T) : (C:ℤ)*d I=(l:ℤ)*incidence V k (fun _ => (1:ℤ)) I := by
    let a : ℤ := (k-I.card).choose (r-I.card)
    let b : ℤ := (V.card-I.card).choose (r-I.card)
    have ha : a≠0 := by dsimp only [a]; exact_mod_cast (Nat.choose_pos (by omega : r-I.card≤k-I.card)).ne'
    have hi : b*l=a*d I := by
      apply (constant_incidence V I r (l:ℤ) (sub I hI) (size I hI)).symm.trans
      simpa [a,d,hI] using (div I hI).choose_spec
    have hc := incidence_incidence (k:=k) V I (size I hI) (fun _ => (1:ℤ))
    rw [incidence_congr ones,constant_incidence _ _ _ _ (sub I hI) (size I hI)] at hc
    change b*C=a*incidence V k (fun _ => (1:ℤ)) I at hc
    apply mul_left_cancel₀ (a:=a) ha
    linear_combination -(C:ℤ)*hi + (l:ℤ)*hc
  apply Int.natCast_dvd_natCast.mp
  use ∑ I∈T, (-1:ℤ)^I.card*d I
  have he := isolate_block hB (fun _ => (1:ℤ))
  calc
    (l:ℤ) = l*(∑ I∈T, (-1:ℤ)^I.card*incidence V k (fun _ => (1:ℤ)) I) := by
      rw [show (∑ I∈T, (-1:ℤ)^I.card*incidence V k (fun _ => (1:ℤ)) I)=1 from he,mul_one]
    _ = (C:ℤ)*(∑ I∈T, (-1:ℤ)^I.card*d I) := by
      rw [mul_sum,mul_sum]
      apply sum_congr rfl
      intro I hI
      linear_combination -((-1:ℤ)^I.card)*(scale I hI)

#print axioms isolate_block
#print axioms small_order_period
end Erdos722.IntegralDesign
