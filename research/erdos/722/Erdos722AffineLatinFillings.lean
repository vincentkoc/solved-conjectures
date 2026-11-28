import Erdos722LatinParameterRecovery

/-! # Realizing the earlier affine transversal equations by Latin cubes -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

/-- In charts on the four symbols the affine equation has a unique solution
in every coordinate. The last chart gives the conventional cube output. -/
def affineCube (g : Symbol → Symbol ≃ Fibre) (u : Fibre) : Quasigroup :=
  ⟨fun x y z => (g 3).symm (g 0 x+g 1 y+g 2 z+u), by
    refine ⟨fun y z x x' eq => ?_,fun x z y y' eq => ?_,fun x y z z' eq => ?_⟩
    · exact (g 0).injective (add_right_cancel (add_right_cancel (add_right_cancel ((g 3).symm.injective eq))))
    · exact (g 1).injective (add_left_cancel (add_right_cancel (add_right_cancel ((g 3).symm.injective eq))))
    · exact (g 2).injective (add_left_cancel (add_right_cancel ((g 3).symm.injective eq)))⟩

theorem affine_graph (g : Symbol → Symbol ≃ Fibre) (u : Fibre) (x : Symbol → Symbol) :
    graph (affineCube g u) x ↔ ∑ j, g j (x j)=u := by
  change (g 3).symm (_+u)=x 3 ↔ _
  rw [Equiv.symm_apply_eq,Fin.sum_univ_four]
  exact (show ∀ a b c v h : Fibre, a+b+c+h=v ↔ a+b+c+v=h by decide +kernel) _ _ _ _ _

/-- Assignment on a numbered base block, before choosing an output coordinate. -/
def affineParameters (d : ℕ) (hd : 6≤d) (a : CosetParameters d) : Parameters d :=
  (fun B =>
    let b : (cubeRule (d+2)).blocks := ⟨B.val,region_sub d B.prop⟩
    affineCube (fun j => symbols.symm.trans (linearCoordinates (cosetColours d hd a.1) b (numbering d B j).val))
      (a.2 b),
   fun B => a.2 ⟨B.val,(mem_sdiff.mp B.prop).1⟩)

theorem affine_accepts (d : ℕ) (hd : 6≤d) (a : CosetParameters d) (B : region d) (f : Base d → Fibre) :
    let b : (cubeRule (d+2)).blocks := ⟨B.val,region_sub d B.prop⟩
    (laws d (affineParameters d hd a).1 B).accepts f ↔
      ∑ i ∈ B.val,linearCoordinates (cosetColours d hd a.1) b i (f i)=a.2 b := by
  let b : (cubeRule (d+2)).blocks := ⟨B.val,region_sub d B.prop⟩
  let D := linearCoordinates (cosetColours d hd a.1) b
  let g (j : Symbol) := symbols.symm.trans (D (numbering d B j).val)
  change graph (affineCube g (a.2 b)) (fun j => symbols (f (numbering d B j).val)) ↔ _
  rw [affine_graph]
  have same := (numbering d B).sum_comp (fun i : B.val => D i.val (f i.val))
  simp only [g,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [same,B.val.sum_coe_sort (fun i => D i (f i))]

/-- If a second completion obeys every chosen local law and the same exterior
rule, then its value on every triple is forced by the patch. -/
theorem patch_agrees {I F : Type*} [DecidableEq I] [DecidableEq F]
    (Q : Rule I) (P T : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (sizes : ∀ B∈S,B.card=4) (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (inside : ∀ i j k (h : baseQuad Q i j k∈S) f, (L ⟨_,h⟩).accepts f →
      T.complete (i,f i) (j,f j) (k,f k)=(Q.complete i j k,f (Q.complete i j k)))
    (outside : ∀ a b c : I × F, baseQuad Q a.1 b.1 c.1∉S → P.complete a b c=T.complete a b c)
    (a b c : I × F) : (patch Q P L sizes proj).complete a b c=T.complete a b c := by
  let w := (patch Q P L sizes proj).complete a b c
  by_cases on : baseQuad Q a.1 b.1 c.1∈S
  · have src : legal Q P L a b c w := (patch_iff ..).mp rfl
    have projection := src.1
    have eq : (packet a b c w).image Prod.fst=baseQuad Q a.1 b.1 c.1 := by
      simp only [packet,image_insert,image_singleton,baseQuad,projection]
    have h := src.2
    unfold packetTest at h
    rw [dif_pos (eq ▸ on)] at h
    obtain ⟨f,law,values⟩ := h
    have ident : (⟨_,eq ▸ on⟩ : S)=⟨_,on⟩ := Subtype.ext eq
    rw [ident] at law
    have hit := inside _ _ _ on f law
    have lift (v : I × F) (hv : v∈packet a b c w) : (v.1,f v.1)=v := Prod.ext rfl (values v hv)
    rw [lift a (by simp [packet]),lift b (by simp [packet]),lift c (by simp [packet]),projection,
      lift w (by simp [packet])] at hit
    exact hit.symm
  · exact (patch_outside Q P L sizes proj a b c on).trans (outside a b c on)

#print axioms affineCube
#print axioms affine_graph
#print axioms affineParameters
#print axioms affine_accepts
#print axioms patch_agrees
end
end Erdos722.LatinFillings
