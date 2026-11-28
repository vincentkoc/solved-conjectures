import Erdos722PrivateMarkedBlocks
import Erdos722CleanAnchorFrame
import Erdos722TransversalIncidence

/-! # Fibre translations in block coordinates with one distinguished incidence per mark -/

namespace Erdos722.FourPoint
open Finset QuadCompletion Equiv
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

def colourPermutation (s : Colour) : Perm Fibre where
  toFun := move s
  invFun := move s⁻¹
  left_inv := move_inv s
  right_inv x := by simpa only [inv_inv] using move_inv s⁻¹ x

abbrev IncidenceColours (Q : Rule I) := Q.blocks → I → Colour

def linearCoordinates {Q : Rule I} (C : IncidenceColours Q) : BlockCoordinates Q :=
  fun B i => colourPermutation (C B i)

/-- The coefficient may differ from the identity only at the marked point of its chosen block. -/
def markedColours {Q : Rule I} {A : Finset I} (m : A → Q.blocks) (c : A → Colour) : IncidenceColours Q :=
  fun B i => if h : i∈A then if m ⟨i,h⟩=B then c ⟨i,h⟩ else 1 else 1

def weightedGradient (Q : Rule I) (C : IncidenceColours Q) : (I → Fibre) →+ BlockOffsets Q where
  toFun t B := ∑ i ∈ B.val, move (C B i) (t i)
  map_zero' := by funext B; exact sum_eq_zero fun _ _ => move_zero _
  map_add' f g := by funext B; simp only [Pi.add_apply,move_add,sum_add_distrib]

theorem markedColour_at {Q : Rule I} {A : Finset I} (m : A → Q.blocks) (c : A → Colour) (q : A) :
    markedColours m c (m q) q.val=c q := by simp [markedColours,q.prop]

theorem markedColour_other {Q : Rule I} {A : Finset I} {m : A → Q.blocks} (inj : Function.Injective m)
    (c : A → Colour) (q : A) {i : I} (neq : i≠q.val) : markedColours m c (m q) i=1 := by
  unfold markedColours
  split
  · rename_i hi
    exact if_neg (fun eq => neq (congrArg Subtype.val (inj eq)))
  · rfl

theorem markedColour_outside {Q : Rule I} {A : Finset I} (m : A → Q.blocks) (c : A → Colour)
    {o : I} (ho : o∉markedSupport m) (B : Q.blocks) (inside : o∈B.val) (i : I) :
    markedColours m c B i=1 := by
  unfold markedColours
  split
  · rename_i hi
    refine if_neg fun eq => ho (mem_biUnion.mpr ⟨⟨i,hi⟩,mem_univ _,?_⟩)
    rwa [eq]
  · rfl

theorem marked_plain {Q : Rule I} {A : Finset I} (M : Matching I) (u : BlockOffsets Q)
    (m : A → Q.blocks) (c : A → Colour) {o : I} (ho : o∉markedSupport m) :
    PlainThrough (blockwiseRule Q M (twistedRule Q M u) (twisted_compatible ..)
      (linearCoordinates (markedColours m c))) o := by
  apply plain_of_chart
  intro S inside
  unfold blockChart
  split
  · rename_i hS
    funext i
    apply Equiv.ext
    intro x
    change move (markedColours m c ⟨S,hS⟩ i) x=x
    rw [markedColour_outside m c ho _ inside,move_one]
  · rfl

theorem weighted_mark_difference {Q : Rule I} {A : Finset I} {m : A → Q.blocks}
    (inj : Function.Injective m) (c : A → Colour) (t : I → Fibre) (q : A) (inside : q.val∈(m q).val) :
    weightedGradient Q (markedColours m c) t (m q)+blockGradient Q t (m q)=move (c q) (t q)+t q := by
  let B := (m q).val
  change (∑ i ∈ B, move (markedColours m c (m q) i) (t i))+(∑ i ∈ B,t i)=_
  have rest : (∑ i ∈ B.erase q.val, move (markedColours m c (m q) i) (t i))=∑ i ∈ B.erase q.val,t i := by
    apply sum_congr rfl
    intro i hi
    rw [markedColour_other inj c q (mem_erase.mp hi).1,move_one]
  rw [← sum_erase_add B _ inside,← sum_erase_add B t inside,rest,markedColour_at]
  calc
    _ = ((∑ i ∈ B.erase q.val,t i)+(∑ i ∈ B.erase q.val,t i))+(move (c q) (t q)+t q) := by ac_rfl
    _ = _ := by rw [fibre_double,zero_add]

#print axioms colourPermutation
#print axioms IncidenceColours
#print axioms linearCoordinates
#print axioms markedColours
#print axioms weightedGradient
#print axioms markedColour_at
#print axioms markedColour_other
#print axioms markedColour_outside
#print axioms marked_plain
#print axioms weighted_mark_difference
end
end Erdos722.FourPoint
