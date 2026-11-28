import Erdos722TypicalPointOrbits
import Erdos722ScaledMatchingError

/-! # Fibre sizes and a finite count of unrestricted point-isomorphism classes -/

namespace Erdos722.FourPoint
open Finset QuadSwitch
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
local instance : Fintype Colour := fintypePerm

def typicalWords (d : ℕ) := (univ : Finset (EdgeWord d)).filter (Typical d)
def typicalClasses (d : ℕ) := (typicalWords d).image (splitClass d)
def splitClasses (d : ℕ) := (univ : Finset (EdgeWord d)).image (splitClass d)

/-- Size of the rooted coordinate group, six times the order of GL(d,2). -/
def rootOrder (d : ℕ) := Nat.card (RootFrames d)

theorem rootOrder_eq (d : ℕ) : rootOrder d=6*Nat.card (Cube d ≃ₗ[ZMod 2] Cube d) := by
  rw [rootOrder,Nat.card_prod,mul_comm]
  have c : Nat.card Colour=6 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [c]

theorem word_partition (d : ℕ) : (typicalWords d).card+(exceptionalWords d).card=6^numberEdges d := by
  change (univ.filter _).card+(univ.filter _).card=_
  rw [card_filter_add_card_filter_not,card_univ,Fintype.card_fun,cubeEdge_card]
  congr 1

private theorem class_size {d : ℕ} (hd : 2≤d) (C) (hC : C∈typicalClasses d) :
    ((typicalWords d).filter fun v => splitClass d v=C).card=rootOrder d := by
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hC
  have h := (mem_filter.mp hw).2
  let S := (typicalWords d).filter fun v => splitClass d v=splitClass d w
  let f (g : RootFrames d) : S := ⟨g • w,mem_filter.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,typical_smul h g⟩,(action_class g w).symm⟩⟩
  have bij : Function.Bijective f := by
    constructor
    · intro g k eq
      have same : g • w=k • w := congrArg Subtype.val eq
      have fix : (k⁻¹*g) • w=w := by rw [mul_smul,same,inv_smul_smul]
      exact (inv_mul_eq_one.mp (((typical_iff_free w).mp h).2 _ fix)).symm
    · rintro ⟨v,hv⟩
      obtain ⟨tv,eq⟩ := mem_filter.mp hv
      obtain ⟨g,hg⟩ := (typical_class_iff hd h (mem_filter.mp tv).2).mp eq.symm
      exact ⟨g,Subtype.ext hg⟩
  exact (Nat.card_eq_finsetCard S).symm.trans (Nat.card_congr (Equiv.ofBijective f bij)).symm

theorem typical_class_mass {d : ℕ} (hd : 2≤d) :
    (typicalClasses d).card*rootOrder d=(typicalWords d).card := by
  have eq := card_eq_sum_card_image (splitClass d) (typicalWords d)
  change _=∑ C∈typicalClasses d,((typicalWords d).filter fun v => splitClass d v=C).card at eq
  rw [eq]
  simp only [sum_congr rfl (class_size hd),sum_const,nsmul_eq_mul,Nat.cast_id]

/-- All classes in the normalized split family, with equality of representatives
taken under arbitrary permutations of the full set of points. -/
theorem split_class_range {d : ℕ} (hd : 2≤d) :
    6^numberEdges d ≤ (splitClasses d).card*rootOrder d+(exceptionalWords d).card ∧
    (splitClasses d).card*rootOrder d ≤ 6^numberEdges d+(exceptionalWords d).card*rootOrder d := by
  let S := typicalClasses d
  let A := splitClasses d
  let B := exceptionalWords d
  have sub : S⊆A := image_subset_image (filter_subset ..)
  have sup : A⊆S∪B.image (splitClass d) := by
    intro C hc
    obtain ⟨w,_,rfl⟩ := mem_image.mp hc
    by_cases h : Typical d w
    · exact mem_union_left _ (mem_image.mpr ⟨w,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨w,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩)
  have lower := Nat.mul_le_mul_right (rootOrder d) (card_le_card sub)
  have upper : A.card≤S.card+B.card := (card_le_card sup).trans
    ((card_union_le ..).trans (Nat.add_le_add_left card_image_le _))
  have up := Nat.mul_le_mul_right (rootOrder d) upper
  change (typicalClasses d).card*rootOrder d≤_ at lower
  change _≤((typicalClasses d).card+B.card)*rootOrder d at up
  rw [typical_class_mass hd] at lower
  rw [Nat.add_mul,typical_class_mass hd] at up
  have part := word_partition d
  change 6^numberEdges d≤A.card*rootOrder d+B.card ∧ A.card*rootOrder d≤6^numberEdges d+B.card*rootOrder d
  change _+B.card=6^numberEdges d at part
  omega

def minimumSystems (d : ℕ) := (splitSystems d).filter fun D =>
  D.IsBlockDesign 3 4 ∧ (binaryIncidence D).rank+(d+1)=4*2^d ∧ Nat.card (automorphisms D)=4*(2^d)^2

theorem minimum_systems_range {d : ℕ} (hd : 2≤d) :
    6^numberEdges d≤(minimumSystems d).card+(exceptionalWords d).card ∧
    (minimumSystems d).card≤6^numberEdges d := by
  have sub : (typicalWords d).image (splitFamily d)⊆minimumSystems d := by
    intro D h
    obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    refine mem_filter.mpr ⟨?_,typical_design hd (mem_filter.mp hw).2⟩
    simp only [splitSystems,mem_image,mem_univ,true_and]
    exact ⟨w,rfl⟩
  have low := card_le_card sub
  rw [card_image_of_injective _ (splitFamily_injective d)] at low
  exact ⟨(word_partition d).symm.trans_le (Nat.add_le_add_right low _),
    (card_le_card (filter_subset ..)).trans_eq (splitSystems_card d)⟩

#print axioms typicalWords
#print axioms typicalClasses
#print axioms splitClasses
#print axioms rootOrder
#print axioms rootOrder_eq
#print axioms word_partition
#print axioms typical_class_mass
#print axioms split_class_range
#print axioms minimumSystems
#print axioms minimum_systems_range
end
end Erdos722.FourPoint
