import Green51ElevenRelations
import Green51FlatSections

/-! # Affine hyperplanes and the augmented columns of a binary set -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51ElevenColumns
local notation "F" => ZMod 2
abbrev V := Cube 11

theorem flat_mono {B A : Finset V} (sub : B⊆A) {p : V} (h : FlatAt B p) :
    FlatAt A p := Green51FlatSections.flat_mono (n:=10) sub h

private theorem cutoff (S : Finset (Cube 10)) (size : S.card=16) : ∃ p, FlatAt S p := by
  obtain ⟨W,p,dim,inside⟩ := Green51FirstSeparation.sixteen_affine S size
  refine ⟨p,W,dim,?_⟩
  rintro y ⟨w,hw,h⟩
  change p+w=y at h
  exact h ▸ inside w hw

/-- Sixteen labels in a ten-dimensional affine hyperplane already force
an affine three-space in the eleven-dimensional double. -/
theorem affine_of_hyperplane (A : Finset V) (large : 16≤A.card) (L : V →ₗ[F] F)
    (non : L≠0) (a : V) (level : ∀x∈A,L x=L a) : ∃p, FlatAt A p :=
  Green51FlatSections.affine_of_hyperplane cutoff A large L non a level

/-- Any sixteen surviving columns of an affine-flat-free configuration
span the full twelve-dimensional augmented space. -/
theorem columns_span (B : Finset V) (large : 16≤B.card) (avoid : ¬∃p,FlatAt B p) :
    Submodule.span F ((fun x:V => ((1:F),x)) '' (B:Set V))=⊤ :=
  Green51FlatSections.columns_span cutoff (by decide) B large avoid

end Green51ElevenColumns
#print axioms Green51ElevenColumns.affine_of_hyperplane
#print axioms Green51ElevenColumns.columns_span
