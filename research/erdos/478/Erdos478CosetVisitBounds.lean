import Erdos478AdjacentFactorialQuotients

/-! # Visits to a target set with a small quotient set -/

namespace Erdos478.QuotientSpacing
open Finset ReturnConcentration
open scoped Classical
noncomputable section

def quotientSet {p : ℕ} (S : Finset (ZMod p)) := S.biUnion fun y => S.image fun x => y*x⁻¹

def hits (p a b : ℕ) (S : Finset (ZMod p)) := (Icc a b).filter fun i => (i.factorial : ZMod p)∈S

theorem target_quotients {p a b : ℕ} (S : Finset (ZMod p)) :
    adjacentQuotients p (hits p a b S) ⊆ quotientSet S := by
  intro u hu
  obtain ⟨e,edge,rfl⟩ := mem_image.mp hu
  obtain ⟨source,dest,_⟩ := links_mem edge
  exact mem_biUnion.mpr ⟨_,(mem_filter.mp dest).2,mem_image.mpr ⟨_,(mem_filter.mp source).2,rfl⟩⟩

/-- The bound holds throughout each interval in the original positive index domain. -/
theorem target_bound {p a b : ℕ} (hp : p.Prime) (ha : 1≤a) (hb : b<p) (S : Finset (ZMod p)) :
    8*((hits p a b S).card-1)^3≤9*(quotientSet S).card*(b-a)^2 := by
  let A := hits p a b S
  have sub : A ⊆ Icc a b := filter_subset ..
  have fits : A ⊆ Ico 1 p := fun i hi =>
    mem_Ico.mpr ⟨ha.trans (mem_Icc.mp (sub hi)).1,lt_of_le_of_lt (mem_Icc.mp (sub hi)).2 hb⟩
  exact (adjacent_quotient_bound hp A fits).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (card_le_card (target_quotients S)))
      (Nat.pow_le_pow_left (width_le sub) 2))

def unitCoset (p : ℕ) [Fact p.Prime] (H : Subgroup (ZMod p)ˣ) (g : (ZMod p)ˣ) :=
  (univ : Finset H).image fun x => ((g*x.val : (ZMod p)ˣ) : ZMod p)

theorem coset_quotient_set (p : ℕ) [Fact p.Prime] (H : Subgroup (ZMod p)ˣ) (g : (ZMod p)ˣ) :
    quotientSet (unitCoset p H g) = (univ : Finset H).image (fun x => (x.val:ZMod p)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨_,hy,tail⟩ := mem_biUnion.mp hu
    obtain ⟨_,hx,rfl⟩ := mem_image.mp tail
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hx
    refine mem_image.mpr ⟨y*x⁻¹,mem_univ _,?_⟩
    change ((y.val*x.val⁻¹ : (ZMod p)ˣ) : ZMod p) = ((g*y.val : (ZMod p)ˣ) : ZMod p)*((g*x.val : (ZMod p)ˣ) : ZMod p)⁻¹
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,mul_inv_rev]
    field_simp
  · intro hu
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hu
    apply mem_biUnion.mpr
    refine ⟨_,mem_image_of_mem _ hy,mem_image.mpr ⟨_,mem_image_of_mem _ (mem_univ (1:H)),?_⟩⟩
    change ((g*y.val : (ZMod p)ˣ) : ZMod p)*((g*1 : (ZMod p)ˣ) : ZMod p)⁻¹ = (y.val : ZMod p)
    simp only [mul_one,Units.val_mul]
    field_simp

/-- A subgroup coset has exactly as many admissible quotients as it has elements. -/
theorem coset_bound (p : ℕ) [hp : Fact p.Prime] (a b : ℕ) (ha : 1≤a) (hb : b<p)
    (H : Subgroup (ZMod p)ˣ) (g : (ZMod p)ˣ) :
    8*((hits p a b (unitCoset p H g)).card-1)^3≤9*Nat.card H*(b-a)^2 := by
  have h := target_bound hp.out ha hb (unitCoset p H g)
  have inj : Function.Injective (fun x : H => (x.val:ZMod p)) := Units.val_injective.comp Subtype.val_injective
  rwa [coset_quotient_set,card_image_of_injective _ inj,card_univ,← Nat.card_eq_fintype_card] at h

#print axioms quotientSet
#print axioms hits
#print axioms target_quotients
#print axioms target_bound
#print axioms unitCoset
#print axioms coset_quotient_set
#print axioms coset_bound
end
end Erdos478.QuotientSpacing
