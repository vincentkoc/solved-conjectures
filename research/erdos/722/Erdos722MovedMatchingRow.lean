import Erdos722MatchingStarEdges
import Erdos722FourFibreFrame

/-! # How many matching arrays can be fixed by a moved base point? -/

namespace Erdos722.FourPoint
open Finset Equiv
open scoped Classical
noncomputable section
variable {I : Type*} [LinearOrder I] [Fintype I]

private theorem crossing_unique {o x y : I} (ne : x≠y) {e f : edges o}
    (ex : e∈incidentEdges o x) (ey : e∈incidentEdges o y)
    (fx : f∈incidentEdges o x) (fy : f∈incidentEdges o y) : e=f := by
  have edge (a : edges o) (hx : a∈incidentEdges o x) (hy : a∈incidentEdges o y) :
      a.val=(min x y,max x y) := by
    have lt := ((mem_edges ..).mp a.prop).2
    rcases (mem_filter.mp hx).2 with h|h <;> rcases (mem_filter.mp hy).2 with k|k
    · exact (ne (h.symm.trans k)).elim
    · have l : x≤y := h ▸ k ▸ lt.le
      rw [min_eq_left l,max_eq_right l,← h,← k]
    · have l : y≤x := h ▸ k ▸ lt.le
      rw [min_eq_right l,max_eq_left l,← h,← k]
    · exact (ne (h.symm.trans k)).elim
  exact Subtype.ext ((edge e ex ey).trans (edge f fx fy).symm)

private theorem row_size {o x y : I} (hx : x≠o) (ne : x≠y) :
    Fintype.card I-3 ≤ (incidentEdges o x \ incidentEdges o y).card := by
  have tiny : ((incidentEdges o x) ∩ (incidentEdges o y)).card≤1 := card_le_one.mpr fun a ha b hb =>
    crossing_unique ne (mem_inter.mp ha).1 (mem_inter.mp ha).2 (mem_inter.mp hb).1 (mem_inter.mp hb).2
  rw [card_sdiff,inter_comm,incident_card hx]
  omega

private theorem transport_from_outside (o : I) (S : Finset (edges o))
    (w v : edges o → Colour) (agree : ∀ e∉S,w e=v e) (i j : I)
    (outside : ∀ e∈S, e.val≠(i,j) ∧ e.val≠(j,i)) :
    (edgeMatching o w).transport i j=(edgeMatching o v).transport i j := by
  change edgeMove o w i j=edgeMove o v i j
  unfold edgeMove
  by_cases h : (i,j)∈edges o
  · simp only [dif_pos h]
    exact agree _ (fun he => (outside _ he).1 rfl)
  · simp only [dif_neg h]
    by_cases k : (j,i)∈edges o
    · simp only [dif_pos k]
      rw [agree _ (fun he => (outside _ he).2 rfl)]
    · simp [k]

/-- Two words fixed by the same frame agree everywhere if they agree off
the moved star (with its single possible crossing edge deleted). -/
private theorem row_determines {o x : I} {b : Perm I} {s : Colour}
    {w v : edges o → Colour}
    (hw : Frame (edgeMatching o w) (edgeMatching o w) b s)
    (hv : Frame (edgeMatching o v) (edgeMatching o v) b s)
    (agree : ∀ e∉incidentEdges o x \ incidentEdges o (b.symm x),w e=v e) : w=v := by
  funext e
  let S := incidentEdges o x \ incidentEdges o (b.symm x)
  by_cases he : e∈S
  · have noY : e.val.1≠b.symm x ∧ e.val.2≠b.symm x := by
      have h := (mem_sdiff.mp he).2
      simpa [incidentEdges] using h
    have outside (f : edges o) (hf : f∈S) :
        f.val≠(b e.val.1,b e.val.2) ∧ f.val≠(b e.val.2,b e.val.1) := by
      have atX := (mem_filter.mp (mem_sdiff.mp hf).1).2
      have bad1 : b e.val.1≠x := fun hh => noY.1 (b.eq_symm_apply.mpr hh)
      have bad2 : b e.val.2≠x := fun hh => noY.2 (b.eq_symm_apply.mpr hh)
      constructor <;> intro eq <;> rw [eq] at atX
      · exact atX.elim bad1 bad2
      · exact atX.elim bad2 bad1
    have tx := transport_from_outside o S w v agree _ _ outside
    have fw := hw e.val.1 e.val.2
    have fv := hv e.val.1 e.val.2
    rw [edge_forward o w e,tx] at fw
    rw [edge_forward o v e] at fv
    exact mul_left_cancel (fw.trans fv.symm)
  · exact agree e he

local instance : Fintype Colour := fintypePerm

/-- For a nonidentity permutation fixing the root, at least n−3 entries
in one moved row are determined by entries outside it. -/
theorem rooted_frame_bound (o : I) (b : Perm I) (s : Colour) (root : b o=o) (nonid : b≠1) :
    ((univ : Finset (edges o → Colour)).filter fun w => Frame (edgeMatching o w) (edgeMatching o w) b s).card ≤
      6^((Fintype.card I-1).choose 2-(Fintype.card I-3)) := by
  obtain ⟨x,moved⟩ : ∃ x, b x≠x := by
    by_contra! same
    exact nonid (Equiv.ext same)
  have hx : x≠o := fun h => moved (h ▸ root)
  have ne : x≠b.symm x := fun h => moved (b.eq_symm_apply.mp h)
  let S := incidentEdges o x \ incidentEdges o (b.symm x)
  let T := (univ : Finset (edges o → Colour)).filter fun w => Frame (edgeMatching o w) (edgeMatching o w) b s
  let f (w : T) (e : ↥((univ : Finset (edges o)) \ S)) := w.val e.val
  have inj : Function.Injective f := by
    intro u v eq
    apply Subtype.ext
    exact row_determines (x:=x) (s:=s) (mem_filter.mp u.prop).2 (mem_filter.mp v.prop).2
      (fun e he => congrFun eq ⟨e,mem_sdiff.mpr ⟨mem_univ _,he⟩⟩)
  have le := Fintype.card_le_of_injective f inj
  have alph : Fintype.card Colour=6 := by decide +kernel
  rw [Fintype.card_coe,Fintype.card_fun,alph,Fintype.card_coe,card_sdiff_of_subset (subset_univ _),
    card_univ,Fintype.card_coe,edges_card] at le
  exact le.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (row_size hx ne) _))

#print axioms rooted_frame_bound
end
end Erdos722.FourPoint
