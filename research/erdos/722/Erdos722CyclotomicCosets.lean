import Erdos722CyclotomicEmbedding
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Multiplicative cosets as difference classes

A coset of an index-`m` subgroup in the nonzero field elements contains
`(q-1)/m` elements and is fixed by multiplication by its subgroup.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

noncomputable def colorSet (H : Subgroup Fˣ) (c : Fˣ ⧸ H) : Finset F :=
  univ.filter fun x => ∃ u : Fˣ, (u:F)=x ∧ (u : Fˣ ⧸ H)=c

theorem mem_color {H : Subgroup Fˣ} {c : Fˣ ⧸ H} {x : F} :
    x ∈ colorSet H c ↔ ∃ u : Fˣ, (u:F)=x ∧ (u : Fˣ ⧸ H)=c := by simp [colorSet]

private def colorEmb (H : Subgroup Fˣ) (v : Fˣ) : H ↪ F :=
  ⟨fun u => ((u.1*v:Fˣ):F),fun _ _ h => Subtype.ext (mul_right_cancel (Units.val_injective h))⟩

private theorem colorSet_mk (H : Subgroup Fˣ) (v : Fˣ) :
    colorSet H (v : Fˣ ⧸ H) = univ.map (colorEmb H v) := by
  ext x
  rw [mem_color]
  simp only [mem_map,mem_univ,true_and]
  constructor
  · rintro ⟨u,rfl,hu⟩
    refine ⟨⟨u/v,QuotientGroup.eq_iff_div_mem.mp hu⟩,?_⟩
    change ((u/v*v:Fˣ):F)=(u:F)
    simp
  · rintro ⟨u,rfl⟩
    exact ⟨u.1*v,rfl,by rw [QuotientGroup.mk_mul,(QuotientGroup.eq_one_iff _).mpr u.2,one_mul]⟩

theorem card_color (H : Subgroup Fˣ) (c : Fˣ ⧸ H) :
    (colorSet H c).card = Nat.card H := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk_surjective c
  classical
  rw [colorSet_mk,card_map,card_univ,Nat.card_eq_fintype_card]

theorem mul_mem_color {H : Subgroup Fˣ} {u : Fˣ} (hu : u∈H) {c : Fˣ ⧸ H}
    {x : F} (hx : x∈colorSet H c) : (u:F)*x ∈ colorSet H c := by
  obtain ⟨v,rfl,hv⟩ := mem_color.mp hx
  exact mem_color.mpr ⟨u*v,rfl,by rw [QuotientGroup.mk_mul,(QuotientGroup.eq_one_iff _).mpr hu,one_mul,hv]⟩

theorem classBounds (H : Subgroup Fˣ) (c : Fˣ ⧸ H) :
    ClassBounds (colorSet H c) (4*H.index) := by
  classical
  have h := H.index_mul_card
  rw [Nat.card_units,Nat.card_eq_fintype_card (α := F)] at h
  refine ⟨?_,colorSet H 1,by rw [card_color,card_color],?_⟩
  · rw [card_color,mul_assoc,h]
    have := Fintype.one_lt_card (α := F)
    omega
  · intro a ha S b
    obtain ⟨u,rfl,hu⟩ := mem_color.mp ha
    have hU := (QuotientGroup.eq_one_iff _).mp hu
    unfold hits
    apply Finset.card_bij (fun z _ => (u:F)*z)
    · intro z hz
      obtain ⟨hD,hS⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mul_mem_color hU hD,by simpa using hS⟩
    · intro x _ y _ he
      exact mul_left_cancel₀ u.ne_zero he
    · intro y hy
      obtain ⟨hD,hS⟩ := mem_filter.mp hy
      have hmul : (u:F)*((↑(u⁻¹):F)*y)=y := by rw [← mul_assoc]; simp
      refine ⟨(↑(u⁻¹):F)*y,mem_filter.mpr ⟨mul_mem_color (H.inv_mem hU) hD,?_⟩,hmul⟩
      simpa only [hmul,one_mul] using hS

/-- An even-order roots-of-unity subgroup of the specified index. -/
theorem exists_even_subgroup (F : Type*) [Field F] [Fintype F] (m a : ℕ)
    (hm : 0<m) (ha : 0<a) (hq : Fintype.card F = m*(2*a)+1) :
    ∃ H : Subgroup Fˣ, H.index=m ∧ (-1:Fˣ)∈H ∧ (-1:F)≠1 := by
  classical
  let H := rootsOfUnity (2*a) F
  have : NeZero (2*a) := ⟨by positivity⟩
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Fˣ)
  rw [Nat.card_units,Nat.card_eq_fintype_card,hq,Nat.add_sub_cancel] at hg
  have ho : orderOf (g^m) = 2*a := by
    rw [orderOf_pow_of_dvd (by omega) (hg ▸ dvd_mul_right m _),hg,Nat.mul_div_cancel_left _ hm]
  have hh : Nat.card H = 2*a := (show IsPrimitiveRoot (g^m) (2*a) from ho ▸ IsPrimitiveRoot.orderOf _).card_rootsOfUnity'
  have hi := H.index_mul_card
  rw [hh,Nat.card_units,Nat.card_eq_fintype_card,hq,Nat.add_sub_cancel] at hi
  refine ⟨H,Nat.eq_of_mul_eq_mul_right (by positivity : 0<2*a) hi,?_,?_⟩
  · apply (mem_rootsOfUnity ..).mpr
    rw [pow_mul]
    simp
  · apply Ring.neg_one_ne_one_of_char_ne_two
    intro hc
    have h := FiniteField.even_card_of_char_two hc
    rw [hq,← mul_assoc,mul_comm m 2,mul_assoc] at h
    omega

#print axioms mem_color
#print axioms mul_mem_color
#print axioms card_color
#print axioms classBounds
#print axioms exists_even_subgroup

end Erdos722.Cyclotomy
