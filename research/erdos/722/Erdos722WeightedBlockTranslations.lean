import Erdos722MarkedIncidence

/-! # How translations change the offsets in blockwise linear coordinates -/

namespace Erdos722.FourPoint
open Finset QuadCompletion Equiv
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I] {Q : Rule I}

abbrev colouredRule (Q : Rule I) (M : Matching I) (C : IncidenceColours Q) (u : BlockOffsets Q) :=
  blockwiseRule Q M (twistedRule Q M u) (twisted_compatible ..) (linearCoordinates C)

private theorem chart_add (C : IncidenceColours Q) (S : Finset I) (i : I) (x y : Fibre) :
    blockChart Q (linearCoordinates C) S i (x+y)=
    blockChart Q (linearCoordinates C) S i x+blockChart Q (linearCoordinates C) S i y := by
  unfold blockChart
  split
  · exact move_add _ _ _
  · rfl

theorem coloured_completion (M : Matching I) (C : IncidenceColours Q) (u : BlockOffsets Q)
    (i j k : I) (x y z : Fibre) :
    let e := blockChart Q (linearCoordinates C) (baseQuad Q i j k)
    e (Q.complete i j k) ((colouredRule Q M C u).complete (i,x) (j,y) (k,z)).2=
      fourth M i j k (e i x) (e j y) (e k z)+transversalOffset Q u i j k := by
  exact Equiv.apply_symm_apply _ _

private theorem gradient_at_triple (C : IncidenceColours Q) (t : I → Fibre) (i j k : I) :
    let e := blockChart Q (linearCoordinates C) (baseQuad Q i j k)
    transversalOffset Q (weightedGradient Q C t) i j k=e i (t i)+e j (t j)+e k (t k)+e (Q.complete i j k) (t (Q.complete i j k)) := by
  let S := baseQuad Q i j k
  let e := blockChart Q (linearCoordinates C) S
  let f (a : I) := e a (t a)
  have equal : transversalOffset Q (weightedGradient Q C t) i j k=transversalOffset Q (blockGradient Q f) i j k := by
    change offsetAt Q (weightedGradient Q C t) S=offsetAt Q (blockGradient Q f) S
    unfold offsetAt
    split
    · rename_i h
      change (∑ a ∈ S, move (C ⟨S,h⟩ a) (t a))=∑ a ∈ S,f a
      apply sum_congr rfl
      intro a _
      exact (show f a=move (C ⟨S,h⟩ a) (t a) by simp only [f,e,blockChart,dif_pos h]; rfl).symm
    · rfl
  exact equal.trans (offset_gradient Q f i j k)

theorem coloured_blocks_injective (M : Matching I) (C : IncidenceColours Q) :
    Function.Injective (fun u : BlockOffsets Q => (colouredRule Q M C u).blocks) := by
  intro u v eq
  apply offset_injective Q
  funext i j k
  have same := completion_determined _ _ eq (i,0) (j,0) (k,0)
  have hu := coloured_completion M C u i j k 0 0 0
  rw [same] at hu
  exact add_left_cancel (hu.symm.trans (coloured_completion M C v i j k 0 0 0))

/-- The unconstrained change of origin in every fibre adds its weighted incidence vector. -/
theorem translation_coloured_blocks (M : Matching I) (C : IncidenceColours Q) (u : BlockOffsets Q) (t : I → Fibre) :
    (pointForm (1 : Perm I) 1 t).finsetCongr.finsetCongr (colouredRule Q M C u).blocks=
      (colouredRule Q M C (u+weightedGradient Q C t)).blocks := by
  apply blocks_of_completion
  rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩
  let v := u+weightedGradient Q C t
  let e := blockChart Q (linearCoordinates C) (baseQuad Q i j k)
  let f (a : I) := e a (t a)
  let l := Q.complete i j k
  simp only [pointForm,Perm.one_apply,move_one,Equiv.coe_fn_mk]
  refine Prod.ext ?_ ?_
  · rfl
  change ((colouredRule Q M C u).complete (i,x) (j,y) (k,z)).2+t l=
    ((colouredRule Q M C v).complete (i,x+t i) (j,y+t j) (k,z+t k)).2
  apply (e l).injective
  rw [chart_add,coloured_completion M C u,coloured_completion M C v,chart_add,chart_add,chart_add]
  rw [translate_fourth M f i j k (e i x) (e j y) (e k z)]
  rw [show transversalOffset Q v i j k=_ from offset_add Q u (weightedGradient Q C t) i j k,
    gradient_at_triple]
  change _+_+f l=_+(f i+f j+f k)+(_+(f i+f j+f k+f l))
  rw [show ∀ a b s d : Fibre, a+s+(b+(s+d))=a+b+d by decide +kernel]

theorem translation_coloured_iff (M : Matching I) (C : IncidenceColours Q) (u v : BlockOffsets Q) (t : I → Fibre) :
    (pointForm (1 : Perm I) 1 t).finsetCongr.finsetCongr (colouredRule Q M C u).blocks=
      (colouredRule Q M C v).blocks ↔ v=u+weightedGradient Q C t := by
  rw [translation_coloured_blocks]
  exact ⟨fun h => coloured_blocks_injective M C h.symm,fun h => h ▸ rfl⟩

#print axioms colouredRule
#print axioms coloured_completion
#print axioms coloured_blocks_injective
#print axioms translation_coloured_blocks
#print axioms translation_coloured_iff
end
end Erdos722.FourPoint
