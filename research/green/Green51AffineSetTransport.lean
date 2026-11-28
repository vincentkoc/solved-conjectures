import Green51AffineFrameRows

/-! # Affine equivalence of finite sets under complements and linear coordinates -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical
variable {U V W : Type*} [AddCommGroup U] [Module F U] [DecidableEq U]
  [AddCommGroup V] [Module F V] [DecidableEq V] [AddCommGroup W] [Module F W] [DecidableEq W]

/-- Affine equivalence of finite sets in possibly different ambient spaces. -/
def AffineRelated (X : Finset U) (Y : Finset V) : Prop :=
  ∃ (e : U ≃ₗ[F] V) (b : V), X.image (fun x => e x+b)=Y

namespace AffineRelated
omit [DecidableEq U] in
theorem linear (X : Finset U) (e : U ≃ₗ[F] V) : AffineRelated X (X.map e.toEquiv.toEmbedding) := by
  exact ⟨e,0,by simp [map_eq_image]⟩

theorem symm {X : Finset U} {Y : Finset V} (h : AffineRelated X Y) : AffineRelated Y X := by
  obtain ⟨e,b,rfl⟩ := h
  exact ⟨e.symm,-e.symm b,by simp [image_image,Function.comp_def]⟩

omit [DecidableEq U] in
theorem trans {X : Finset U} {Y : Finset V} {Z : Finset W}
    (a : AffineRelated X Y) (b : AffineRelated Y Z) : AffineRelated X Z := by
  obtain ⟨e,u,rfl⟩ := a
  obtain ⟨f,v,rfl⟩ := b
  exact ⟨e.trans f,f u+v,by simp [image_image,Function.comp_def,add_assoc]⟩

theorem compl [Fintype U] [Fintype V] {X : Finset U} {Y : Finset V}
    (h : AffineRelated X Y) : AffineRelated Xᶜ Yᶜ := by
  obtain ⟨e,b,rfl⟩ := h
  let f := e.toEquiv.trans (Equiv.addRight b)
  refine ⟨e,b,?_⟩
  change Xᶜ.image f = (X.image f)ᶜ
  ext y
  obtain ⟨x,rfl⟩ := f.surjective y
  simp [mem_image]

end AffineRelated
end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.AffineRelated.linear
#print axioms Green51FrameIsomorphisms.AffineRelated.symm
#print axioms Green51FrameIsomorphisms.AffineRelated.trans
#print axioms Green51FrameIsomorphisms.AffineRelated.compl
