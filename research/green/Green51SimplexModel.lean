import Green51FifteenSection
import Green51SystematicChecks
import Green51PairedTypes

/-! # A representative for the fifteen-point orbit -/

open Finset Green50Downsets Green50Sharp Green51SystematicChecks Green51TenDimensions
open scoped Pointwise
namespace Green51SimplexSection
local notation "V" => Cube 10

def units : List ℕ := [0,1,2,4,8,16,32,64,128,256,512]
def extras : List ℕ := [685,822,967,1016]
def model : Finset V := rows 10 units ∪ rows 10 extras

theorem model_card : model.card=15 := by decide +kernel

theorem model_free (T : Finset V) (sub : T⊆model) (sz : T.card=4 ∨ T.card=6) :
    (∑ t∈T,t)≠0 := by
  have ok : test 10 0 0 extras=true := by decide +kernel
  have heavy (U : Finset V) (sub : U⊆rows 10 extras) (non : U.Nonempty) :
      6<U.card+(supp (∑ u∈U,u)).card := by
    have h := test_sound 10 extras 0 0 ok U sub
    have zero : point 10 0 = 0 := by funext i; simp [point]
    simpa only [Nat.zero_add,zero,zero_add,show U.card≠0 from ne_of_gt (card_pos.mpr non),false_or] using h
  have check : units.all (fun v => decide ((supp (point 10 v)).card≤1))=true := by decide +kernel
  have small (x) (hx : x∈rows 10 units) : (supp x).card≤1 := by
    obtain ⟨v,hv,rfl⟩ := (mem_rows units).mp hx
    simpa using List.all_eq_true.mp check v hv
  have inc : model⊆ball 10 1 ∪ rows 10 extras := union_subset_union
    (fun x hx => mem_filter.mpr ⟨mem_univ _,small x hx⟩) Subset.rfl
  exact Green51SmallWitnesses.add_labels_of_distance _ heavy T (sub.trans inc) sz

theorem model_no_affine : ¬∃ p, FlatAt model p := by
  have no : ¬FlatAt model 0 := by
    intro h
    obtain ⟨T,sub,sz,zero⟩ := (Green51SparseDimensions.linear_three_iff model
      (by rw [model_card];decide)).mp ((flat_zero model).mp h)
    exact model_free T sub sz zero
  rintro ⟨p,h⟩
  obtain ⟨T,sub,sz,_⟩ := Green51PairedTypes.sixteen_relation no h
  have bound := card_le_card sub
  rw [sz,model_card] at bound
  omega

/-- Every extremal fifteen-label set avoiding an affine three-space in ten
binary dimensions can be sent onto the displayed representative. -/
theorem normal_form (A : Finset V) (size : A.card=15) (avoid : ¬FlatAt A 0) :
    ∃ (g : V ≃ₗ[ZMod 2] V) (t : V), A.image (fun x => g x+t)=model := by
  apply affine_unique A model size model_card _ model_free
  intro T sub sz zero
  exact avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A
    (by rw [size];decide)).mpr ⟨T,sub,sz,zero⟩))

end Green51SimplexSection
#print axioms Green51SimplexSection.model_card
#print axioms Green51SimplexSection.model_free
#print axioms Green51SimplexSection.model_no_affine
#print axioms Green51SimplexSection.normal_form
