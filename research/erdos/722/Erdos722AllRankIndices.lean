import Erdos722SmallOrderIndices

/-!
# All sufficiently large admissible indices in every rank

At fixed point, block and subset sizes, choose a signed design for each
admissible residue modulo the complete design index. A uniform increase
of all block weights makes the multiplicities nonnegative.
-/

namespace Erdos722.IntegralDesign
open Finset Filter
variable {α : Type*} [DecidableEq α]

/-- All allowed parameter triples, including orders below k+r. -/
theorem uniform_signed_iff (V : Finset α) {r k : ℕ} (hrk : r≤k) (hkv : k≤V.card) (l : ℕ) :
    (∃ w, Represents V r k (fun _ => (l:ℤ)) w) ↔ Conditions V.card r k l := by
  by_cases h : k+r≤V.card
  · exact signed_index_iff V hrk h l
  refine ⟨fun ⟨_,hw⟩ => (admissible_constant V (hrk.trans hkv)).mp (admissible_of_represents hw),?_⟩
  intro hl
  obtain ⟨w,hw⟩ := multiples_realized V hrk ((small_order_period V hrk hkv (by omega)).mp hl)
  refine ⟨fun B => (w B:ℤ),fun A hA => ?_⟩
  change (∑ B∈(V.powersetCard k).filter (A⊆·), (w B:ℤ))=(l:ℤ)
  rw [← Nat.cast_sum,hw A hA]

/-- With the order and both ranks fixed, admissibility characterizes the
indices of designs allowing repeated blocks for all sufficiently large indices. -/
theorem eventual_index_spectrum (V : Finset α) {r k : ℕ} (hrk : r≤k) (hkv : k≤V.card) :
    ∀ᶠ l : ℕ in atTop, Multiplicities V r k l ↔ Conditions V.card r k l := by
  classical
  let C := (V.card-r).choose (k-r)
  have hC : 0<C := Nat.choose_pos (by omega)
  have hc := complete_conditions V hrk (hrk.trans hkv)
  have representatives (s : ℕ) : ∃ w, Conditions V.card r k s → Represents V r k (fun _ => (s:ℤ)) w := by
    by_cases h : Conditions V.card r k s
    · obtain ⟨w,hw⟩ := (uniform_signed_iff V hrk hkv s).mpr h
      exact ⟨w,fun _ => hw⟩
    · exact ⟨0,fun he => (h he).elim⟩
  choose w hw using representatives
  let blocks := V.powersetCard k
  let mass s := ∑ B∈blocks, (w s B).natAbs
  let L := ∑ s∈range C, mass s
  filter_upwards [eventually_ge_atTop (L*C)] with l hl
  refine ⟨conditions_of_multiplicities (hrk.trans hkv),?_⟩
  intro H
  let s := l%C
  let t := l/C
  have hs : Conditions V.card r k s := conditions_mod hc H
  have ht : L≤t := (Nat.le_div_iff_mul_le hC).mpr hl
  have hn (B : Finset α) (hB:B∈blocks) : 0≤w s B+(t:ℤ) := by
    have h₁ : (w s B).natAbs≤mass s := single_le_sum (f:=fun A => (w s A).natAbs) (fun _ _ => Nat.zero_le _) hB
    have h₂ : mass s≤L := single_le_sum (f:=mass) (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.mod_lt l hC))
    have h₃ : -w s B≤((w s B).natAbs:ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
    omega
  refine ⟨fun B => (w s B+(t:ℤ)).toNat,fun A hA => ?_⟩
  let bs := blocks.filter (A⊆·)
  obtain ⟨hAv,hAr⟩ := mem_powersetCard.mp hA
  have hcard : bs.card=C := by
    rw [show bs=(V.powersetCard k).filter (A⊆·) from rfl,card_filter_powersetCard_subset _ _ _ hAv (hAr ▸ hrk),hAr]
  apply Int.ofNat_inj.mp
  push_cast
  calc
    _ = ∑ B∈bs, (w s B+(t:ℤ)) := sum_congr rfl (fun B hB => Int.toNat_of_nonneg (hn B (mem_filter.mp hB).1))
    _ = (s:ℤ)+(C:ℤ)*t := by
      have hsum : (∑ B∈bs, w s B)=(s:ℤ) := hw s hs A hA
      rw [sum_add_distrib,hsum,sum_const,hcard,nsmul_eq_mul]
    _ = (l:ℤ) := by exact_mod_cast Nat.mod_add_div l C

#print axioms uniform_signed_iff
#print axioms eventual_index_spectrum
end Erdos722.IntegralDesign
