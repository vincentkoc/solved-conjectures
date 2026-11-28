import Erdos722AffineParallelClasses
import Mathlib.Data.Finset.Sum

/-!
# Completing a square-order pair design

Index directions by the pencil at one point. Give every old line its
direction as an extra point and put all directions on the line at infinity.
The resulting Steiner pair design has the parameters of a projective plane.
-/

namespace Erdos722.InversiveOrder
open Finset Quartet MinimumOrder
open scoped Classical
noncomputable section

private def extended {P I D : Type*} [Fintype D]
    (line : I → Finset P) (direction : I → D) : Option I → Finset (P ⊕ D)
  | none => (∅ : Finset P).disjSum univ
  | some i => (line i).disjSum {direction i}

private theorem mixed_line {P I D : Type*} [Fintype D] (line : I → Finset P)
    (direction : I → D) (p : P) (d : D)
    (h : ∃! i, p∈line i ∧ direction i=d) :
    ∃! i, Sum.inl p∈extended line direction i ∧ Sum.inr d∈extended line direction i := by
  obtain ⟨i,hi,hu⟩ := h
  refine ⟨some i,by simpa [extended,eq_comm] using hi,?_⟩
  rintro (_|j) hj
  · simpa [extended] using hj.1
  · exact congrArg some (hu j (by simpa [extended,eq_comm] using hj))

/-- Complete a uniform pair cover with a direction for each line: at a
finite point there is exactly one line in each direction. -/
theorem complete_by_directions {P I D : Type*} [Fintype D] {q : ℕ}
    (line : I → Finset P) (direction : I → D) (hc : Fintype.card D=q+1)
    (hl : ∀ i, (line i).card=q)
    (hpair : ∀ p p' : P, p≠p' → ∃! i, p∈line i ∧ p'∈line i)
    (hdir : ∀ (p : P) (d : D), ∃! i, p∈line i ∧ direction i=d) :
    Nonempty (Cover (P ⊕ D) (AllPairs _) (·=q+1)) := by
  classical
  refine ⟨Cover.ofLines (extended line direction) ?_ (fun _ _ _ _ _ _ => trivial) ?_⟩
  · rintro (_|i) <;> simp [extended,hl,hc]
  · rintro (p|d) (p'|d') hne _
    · obtain ⟨i,hi,hu⟩ := hpair p p' (fun e => hne (congrArg Sum.inl e))
      refine ⟨some i,by simpa [extended] using hi,?_⟩
      rintro (_|j) hj
      · simpa [extended] using hj.1
      · exact congrArg some (hu j (by simpa [extended] using hj))
    · exact mixed_line line direction p d' (hdir p d')
    · simpa only [and_comm] using mixed_line line direction p' d (hdir p' d)
    · refine ⟨none,by simp [extended],?_⟩
      rintro (_|j) hj
      · rfl
      · have hh : d=direction j ∧ d'=direction j := by simpa [extended] using hj
        exact (hne (congrArg Sum.inr (hh.1.trans hh.2.symm))).elim

/-- Every ordinary `2-(q²,q,1)` design completes to a projective-order
pair design with q+1 points on each block. -/
theorem complete_affine_design {q : ℕ} (hq : 2≤q) {H : Finset (Finset (Fin (q^2)))}
    (hH : H.IsBlockDesign 2 q) :
    ∃ G : Finset (Finset (Fin (q*(q+1)+1))), G.IsBlockDesign 2 (q+1) := by
  classical
  let P := Fin (q^2)
  let o : P := ⟨0,by positivity⟩
  let pencil := H.filter (o∈·)
  let D := (pencil : Type)
  let I := (H : Type)
  let direction (i : I) : D :=
    ⟨(parallel_through hq hH i.property o).choose,
      mem_filter.mpr ⟨(parallel_through hq hH i.property o).choose_spec.1.1,
        (parallel_through hq hH i.property o).choose_spec.1.2.1⟩⟩
  have hd (i : I) : Parallel (direction i).val i.val :=
    (parallel_through hq hH i.property o).choose_spec.1.2.2
  have hdir (i : I) (d : D) : direction i=d ↔ Parallel i.val d.val := by
    constructor
    · rintro rfl
      exact parallel_symm (hd i)
    · intro h
      apply Subtype.ext
      exact ((parallel_through hq hH i.property o).choose_spec.2 d.val
        ⟨(mem_filter.mp d.property).1,(mem_filter.mp d.property).2,parallel_symm h⟩).symm
  have hc : Fintype.card D=q+1 := (Fintype.card_coe pencil).trans (affine_pencil_card hq hH o)
  obtain ⟨C⟩ := complete_by_directions (P:=P) (I:=I) Subtype.val direction hc
    (fun i => hH.1 _ i.property) (fun p p' hp => by
      obtain ⟨B,hB,hu⟩ := pair_line hH hp
      exact ⟨⟨B,hB.1⟩,hB.2,fun i hi => Subtype.ext (hu _ ⟨i.property,hi⟩)⟩) (fun p d => by
      obtain ⟨B,hB,hu⟩ := parallel_through hq hH (mem_filter.mp d.property).1 p
      exact ⟨⟨B,hB.1⟩,⟨hB.2.1,(hdir _ d).mpr hB.2.2⟩,fun i hi =>
        Subtype.ext (hu _ ⟨i.property,hi.1,(hdir _ d).mp hi.2⟩)⟩)
  have hsize : Fintype.card (P ⊕ D)=q*(q+1)+1 := by simp [P,hc]; ring
  exact (C.has hsize).some.design

theorem projective_plane_of_affine_design {q : ℕ} (hq : 2≤q) {H : Finset (Finset (Fin (q^2)))}
    (hH : H.IsBlockDesign 2 q) :
    ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : Configuration.ProjectivePlane P L), pp.order=q := by
  obtain ⟨G,hG⟩ := complete_affine_design hq hH
  exact projective_plane_of_symmetric_pairs hq hG

#print axioms complete_by_directions
#print axioms complete_affine_design
#print axioms projective_plane_of_affine_design
end
end Erdos722.InversiveOrder
