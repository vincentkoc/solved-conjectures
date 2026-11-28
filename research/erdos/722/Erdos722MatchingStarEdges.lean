import Erdos722FourFibreEdges
import Erdos722DeterminedMatchingEdges

/-! # Independent entries in a nonroot star of a matching array -/

namespace Erdos722.FourPoint
open Finset Equiv
open scoped Classical
noncomputable section
variable {I : Type*} [LinearOrder I] [Fintype I]

def incidentEdges (o x : I) : Finset (edges o) := univ.filter fun e => e.val.1=x ∨ e.val.2=x

/-- Sorting an edge with one endpoint at x identifies its possible partners
with all labels except the root and x. -/
theorem incident_card {o x : I} (hx : x≠o) : (incidentEdges o x).card=Fintype.card I-2 := by
  classical
  let T := ((univ : Finset I).erase o).erase x
  let N := incidentEdges o x
  let f (e : N) : I := if e.val.val.1=x then e.val.val.2 else e.val.val.1
  have incident (e : N) : e.val.val.1=x ∨ e.val.val.2=x := (mem_filter.mp e.prop).2
  have facts (e : N) := (mem_edges o e.val.val.1 e.val.val.2).mp e.val.prop
  have hf (e : N) : f e∈T := by
    have h := facts e
    rcases incident e with a|b
    · have ne : e.val.val.2≠x := by rw [← a]; exact h.2.ne'
      simp [f,a,T,ne,h.1.2]
    · have ne : e.val.val.1≠x := by rw [← b]; exact h.2.ne
      simp [f,ne,T,h.1.1]
  have recover (e : N) : e.val.val=(min x (f e),max x (f e)) := by
    have h := facts e
    rcases incident e with a|b
    · have le : x≤e.val.val.2 := a ▸ h.2.le
      rw [show f e=e.val.val.2 from if_pos a,min_eq_left le,max_eq_right le,← a]
    · have ne : e.val.val.1≠x := by rw [← b]; exact h.2.ne
      have le : e.val.val.1≤x := b ▸ h.2.le
      rw [show f e=e.val.val.1 from if_neg ne,min_eq_right le,max_eq_left le,← b]
  let g (e : N) : T := ⟨f e,hf e⟩
  have bij : Function.Bijective g := by
    constructor
    · intro a b h
      have hf' := congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext
      rw [recover a,recover b]
      change f a=f b at hf'
      rw [hf']
    · intro z
      have hz := mem_erase.mp z.prop
      have ho := (mem_erase.mp hz.2).1
      rcases lt_or_gt_of_ne hz.1 with h|h
      · let e : edges o := ⟨(z.val,x),(mem_edges ..).mpr ⟨⟨ho,hx⟩,h⟩⟩
        refine ⟨⟨e,mem_filter.mpr ⟨mem_univ _,Or.inr rfl⟩⟩,?_⟩
        exact Subtype.ext (if_neg hz.1)
      · let e : edges o := ⟨(x,z.val),(mem_edges ..).mpr ⟨⟨hx,ho⟩,h⟩⟩
        refine ⟨⟨e,mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩⟩,?_⟩
        exact Subtype.ext (if_pos rfl)
  have card := Fintype.card_congr (Equiv.ofBijective g bij)
  rw [Fintype.card_coe,Fintype.card_coe,card_erase_of_mem (mem_erase.mpr ⟨hx,mem_univ _⟩),
    card_erase_of_mem (mem_univ o),card_univ] at card
  exact card

theorem normalized_at_iff (o x : I) (w : edges o → Colour) :
    Normalized (edgeMatching o w) x ↔ ∀ e∈incidentEdges o x,w e=1 := by
  constructor
  · intro h e he
    rw [← edge_forward o w e]
    rcases (mem_filter.mp he).2 with a|b
    · rw [a]; exact h _
    · rw [b,(edgeMatching o w).reverse x e.val.1,h,inv_one]
  · intro h j
    change edgeMove o w x j=1
    unfold edgeMove
    split
    · rename_i good
      exact h ⟨(x,j),good⟩ (mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩)
    · split
      · rename_i good
        rw [h ⟨(j,x),good⟩ (mem_filter.mpr ⟨mem_univ _,Or.inr rfl⟩),inv_one]
      · rfl

local instance : Fintype Colour := fintypePerm

/-- A specified second identity star consumes exactly n−2 independent
entries in the normalized word. -/
theorem second_star_count {o x : I} (hx : x≠o) :
    ((univ : Finset (edges o → Colour)).filter fun w => Normalized (edgeMatching o w) x).card =
      6^((Fintype.card I-1).choose 2-(Fintype.card I-2)) := by
  have eq := determined_edges (A:=Colour) (incidentEdges o x) (fun _ _ _ => 1)
  have colours : Fintype.card Colour=6 := by decide +kernel
  have count : Fintype.card ↥(edges o)=(Fintype.card I-1).choose 2 := (Fintype.card_coe _).trans (edges_card o)
  rw [colours,count,incident_card hx] at eq
  refine Eq.trans (congrArg Finset.card ?_) eq
  ext w
  simp only [mem_filter,mem_univ,true_and]
  exact normalized_at_iff o x w

#print axioms normalized_at_iff
#print axioms second_star_count
#print axioms incidentEdges
#print axioms incident_card
end
end Erdos722.FourPoint
