import Green51SystematicChecks
import Green51PairedTypes
import Green51OddCircuitSlices

/-! # A twenty-label affine three-space obstruction in twelve dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51SystematicChecks
open scoped Pointwise symmDiff
namespace Green51TwelveAffineWitness
local notation "V" => Cube 12

private def units : List ℕ := [0,1,2,4,8,16,32,64,128,256,512,1024,2048]
private def extra : List ℕ := [1719,3480,3753,378,3846,1738,2759]

/-- The zero label, twelve independent binary unit columns, and seven check columns. -/
def labels : Finset V := rows 12 units ∪ rows 12 extra

theorem labels_card : labels.card = 20 := by decide +kernel

private theorem free (T : Finset V) (sub : T⊆labels) (sz : T.card=4 ∨ T.card=6) :
    (∑ x∈T,x) ≠ 0 := by
  have ok : test 12 0 0 extra = true := by decide +kernel
  have heavy (U : Finset V) (sub : U⊆rows 12 extra) (non : U.Nonempty) :
      6 < U.card+(supp (∑ u∈U,u)).card := by
    have b := test_sound 12 extra 0 0 ok U sub
    have z : point 12 0 = 0 := by funext i; simp [point]
    simpa only [Nat.zero_add,z,zero_add,show U.card≠0 from ne_of_gt (card_pos.mpr non),false_or] using b
  have unitWeights : units.all (fun v => decide ((supp (point 12 v)).card ≤ 1)) = true := by
    decide +kernel
  have small (x) (hx : x ∈ rows 12 units) : (supp x).card ≤ 1 := by
    obtain ⟨v, hv, rfl⟩ := (mem_rows units).mp hx
    simpa using List.all_eq_true.mp unitWeights v hv
  have inc : labels ⊆ ball 12 1 ∪ rows 12 extra :=
    union_subset_union (fun x hx => mem_filter.mpr ⟨mem_univ _, small x hx⟩) Subset.rfl
  exact Green51SmallWitnesses.add_labels_of_distance _ heavy T (sub.trans inc) sz

/-- If twenty labels have no four- or six-point relations and their sum is a
pair of distinct labels, their double contains no affine three-space. -/
theorem no_affine_of_total_pair {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    [Fintype G] [DecidableEq G] (A P : Finset G) (sz : A.card=20) (pair : P.card=2)
    (inc : P⊆A) (total : (∑ x∈A,x) = ∑ x∈P,x)
    (noRel : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ x∈T,x)≠0) :
    ¬∃ p, FlatAt A p := by
  have noLin : ¬FlatAt A 0 := by
    intro flat
    obtain ⟨T,sub,n,h⟩ := (Green51SparseDimensions.linear_three_iff A (by omega)).mp
      ((flat_zero A).mp flat)
    exact noRel T sub n h
  rintro ⟨p,flat⟩
  obtain ⟨B,sub,n,zero⟩ := Green51PairedTypes.sixteen_relation noLin flat
  let S := A \ B
  have four : S.card=4 := by dsimp [S]; rw [card_sdiff_of_subset sub,sz,n]
  have eq : (∑ x∈S,x) = ∑ x∈P,x := by
    have h := sum_sdiff sub (f:=id)
    simpa only [id_eq,zero,add_zero,total] using h
  have zero' := Green51FourSpace.subset_sum_add id S P
  change (∑ x∈S ∆ P,x)=(∑ x∈S,x)+∑ x∈P,x at zero'
  rw [eq,ZModModule.add_self] at zero'
  have inter : (S∩P).card≤2 := (card_le_card inter_subset_right).trans_eq pair
  have wt := (Green51GirthFrame.card_symmDiff_parts S P).2
  rw [four,pair] at wt
  have cases : (S∆P).card=2 ∨ (S∆P).card=4 ∨ (S∆P).card=6 := by omega
  rcases cases with two | other
  · obtain ⟨u,v,ne,h⟩ := card_eq_two.mp two
    rw [h,sum_pair ne] at zero'
    exact ne (add_right_cancel (zero'.trans (ZModModule.add_self v).symm))
  · apply noRel (S∆P) _ other zero'
    intro x hx
    rcases mem_symmDiff.mp hx with h|h
    · exact sdiff_subset h.1
    · exact inc h.1

/-- The double of the twenty labels contains no affine three-space. -/
theorem no_affine : ¬∃ p, FlatAt labels p :=
  no_affine_of_total_pair labels {point 12 8, point 12 2048} labels_card
    (by decide +kernel) (by decide +kernel) (by decide +kernel) free

end Green51TwelveAffineWitness
#print axioms Green51TwelveAffineWitness.labels_card
#print axioms Green51TwelveAffineWitness.no_affine_of_total_pair
#print axioms Green51TwelveAffineWitness.no_affine
