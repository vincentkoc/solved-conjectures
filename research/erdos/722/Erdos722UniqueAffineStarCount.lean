import Erdos722DisjointAffineStarClasses

/-! # Counting asymmetric Steiner quadruple systems with an intrinsic affine star -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec offsetFinite choiceFintype
variable {d : ℕ} {hd : 6≤d}

/-- Exact count for the specified layout, on the quotient by all point permutations. -/
theorem star_class_count (L : Layout d hd) : (starClasses L).card=
    13824^(FreeSites L).card*13608^L.markers.card*4^(blockNumber (2^(d+2))-2^(d+2)) := by
  let n := 2^(d+2)
  let b := blockNumber n
  have all : (cubeRule (d+2)).blocks.card=b := by
    rw [base_block_count (cubeRule (d+2)).isBlockDesign]
    simp [b,n,blockNumber,Cube]
  have interiorCard : (interior L).card=b-L.exterior.card := by rw [interior,card_sdiff_of_subset L.sub,all]
  have m := card_le_card L.marked
  have e := card_le_card L.sub
  rw [interiorCard] at m
  rw [all] at e
  have f : (FreeSites L).card=b-L.exterior.card-L.markers.card := by
    rw [FreeSites,card_sdiff_of_subset L.marked,interiorCard]
  have inject := Nat.card_le_card_of_injective _ (measurements_injective L)
  have compare : 4^n≤4^L.exterior.card := by
    simpa [n,ExteriorOffsets,Base,Cube,Fibre,Nat.card_eq_fintype_card] using inject
  have le := (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp compare
  have exponent : L.markers.card+(FreeSites L).card+(L.exterior.card-n)=b-n := by omega
  rw [starClasses,card_image_of_injective _ (starClass_injective L),card_univ,← Nat.card_eq_fintype_card]
  simp only [Choices,LocalChoices,Nat.card_prod,Nat.card_fun,Nonlinear,
    nonlinear_cube_count,latin_cube_count,offset_class_count]
  rw [Nat.card_eq_fintype_card (α:=L.markers),Nat.card_eq_fintype_card (α:=FreeSites L),Fintype.card_coe,Fintype.card_coe]
  change (54432^L.markers.card*55296^(FreeSites L).card)*4^(L.exterior.card-n)=
    13824^(FreeSites L).card*13608^L.markers.card*4^(b-n)
  rw [← exponent,show 54432=13608*4 by decide,show 55296=13824*4 by decide,mul_pow,mul_pow,pow_add,pow_add]
  ring

/-- Guaranteed number of sites left after reserving one pencil and up to 2n detecting equations. -/
def siteBound (d : ℕ) := blockNumber (2^(d+2)) - ((2^(d+2)-1).choose 2 / 3 + 2*2^(d+2))

private theorem weighted_lower (f m N M : ℕ) (total : N≤f+m) (mark : m≤M) :
    13824^(N-M)*13608^(min N M) ≤ 13824^f*13608^m := by
  have free : N-M≤f := by omega
  have rest : min N M≤(f-(N-M))+m := by omega
  calc
    _ ≤ 13824^(N-M)*13608^((f-(N-M))+m) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) rest)
    _ = 13824^(N-M)*13608^(f-(N-M))*13608^m := by rw [pow_add,mul_assoc]
    _ ≤ 13824^(N-M)*13824^(f-(N-M))*13608^m :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _))
    _ = _ := by rw [← pow_add,Nat.add_sub_of_le free]

theorem star_count_lower (L : Layout d hd) :
    13824^(siteBound d-(2^(d+2)-1))*13608^(min (siteBound d) (2^(d+2)-1))*
      4^(blockNumber (2^(d+2))-2^(d+2)) ≤ (starClasses L).card := by
  rw [star_class_count]
  apply Nat.mul_le_mul_right
  apply weighted_lower _ _ _ _ _ L.marker_bound
  have star := pencil_card (cubeRule (d+2)) 0
  rw [show Fintype.card (Cube (d+2))=2^(d+2) by simp [Cube]] at star
  have ext := L.exterior_bound
  have all : (cubeRule (d+2)).blocks.card=blockNumber (2^(d+2)) := by
    rw [base_block_count (cubeRule (d+2)).isBlockDesign]
    simp [blockNumber,Cube]
  have m := card_le_card L.marked
  change L.markers.card≤(interior L).card at m
  rw [interior,card_sdiff_of_subset L.sub,all] at m
  rw [FreeSites,card_sdiff_of_subset L.marked,card_sdiff_of_subset L.sub,all,siteBound]
  omega

/-- On 1024 points these additional classes are disjoint from the entire coset family. -/
theorem additional_1024 (L : Layout 6 (by decide)) :
    13824^679318*13608^255*4^690624 ≤ (starClasses L \ latinClasses 6 (by decide)).card := by
  rw [sdiff_eq_left.mpr (disjoint_coset_classes L)]
  have free : siteBound 6=679573 := by rw [siteBound,blockNumber_formula]; decide +kernel
  have gap : blockNumber (2^(6+2))-2^(6+2)=690624 := by rw [blockNumber_formula]; decide +kernel
  have lower := star_count_lower L
  rw [free,gap,show 679573-(2^(6+2)-1)=679318 by decide,show min 679573 (2^(6+2)-1)=255 by decide] at lower
  exact lower

/-- For each order, the entire additional lower bound is witnessed by a single set of
unrestricted point-isomorphism classes of canonical Steiner quadruple systems. -/
theorem additional_families (d : ℕ) (hd : 6≤d) :
    ∃ C : Finset (DesignClass (Fin (4*2^(d+2)))), Disjoint C (latinClasses d hd) ∧
      13824^(siteBound d-(2^(d+2)-1))*13608^(min (siteBound d) (2^(d+2)-1))*
        4^(blockNumber (2^(d+2))-2^(d+2)) ≤ C.card ∧
      ∀ y∈C, ∃ D : Finset (Finset (Fin (4*2^(d+2)))), classOf D=y ∧ D.IsBlockDesign 3 4 ∧
        (binaryIncidence D).rank+(d+3)=4*2^(d+2) ∧ ∀ e : automorphisms D, e=1 := by
  obtain ⟨L⟩ := layout_exists d hd
  exact ⟨starClasses L,disjoint_coset_classes L,star_count_lower L,star_members L⟩

#print axioms additional_families
#print axioms star_class_count
#print axioms siteBound
#print axioms star_count_lower
#print axioms additional_1024
end
end Erdos722.AffineStar
