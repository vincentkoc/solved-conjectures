import Green51AffineFrameRows
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # A linear relation space for configurations with independent row translations -/

namespace Green51FrameIsomorphisms
open Green53ParityThreshold
open scoped Classical
variable {H I : Type*} [AddCommGroup H] [Module F H] [FiniteDimensional F H]

private theorem rotate_of_ker {V : Type*} [AddCommGroup V] [Module F V]
    (f g : V →ₗ[F] H) (same : LinearMap.ker f=LinearMap.ker g) :
    ∃ u : H ≃ₗ[F] H, ∀ v, u (f v)=g v := by
  let q := Submodule.quotEquivOfEq _ _ same
  let h := (f.quotKerEquivRange.symm.trans q).trans g.quotKerEquivRange
  obtain ⟨u,hu⟩ := Submodule.exists_linearEquiv_restrict_eq h
  refine ⟨u,fun x => ?_⟩
  let y : LinearMap.range f := ⟨f x,⟨x,rfl⟩⟩
  have samePoint := (hu y).symm
  change u (f x)=(g.quotKerEquivRange (q (f.quotKerEquivRange.symm y)) : H) at samePoint
  rw [show f.quotKerEquivRange.symm y = (LinearMap.ker f).mkQ x from f.quotKerEquivRange_symm_apply_image x _] at samePoint
  exact samePoint.trans (g.quotKerEquivRange_apply_mk x)

theorem tuple_ker_iff (a b : I → H) :
    LinearMap.ker (Finsupp.linearCombination F a)=LinearMap.ker (Finsupp.linearCombination F b) ↔
    ∃ u : H ≃ₗ[F] H, ∀ i,u (a i)=b i := by
  constructor
  · intro same
    obtain ⟨u,hu⟩ := rotate_of_ker _ _ same
    exact ⟨u,fun i => by simpa using hu (Finsupp.single i 1)⟩
  · rintro ⟨u,hu⟩
    have cmp : u.toLinearMap.comp (Finsupp.linearCombination F a)=Finsupp.linearCombination F b := by
      apply Finsupp.lhom_ext'
      intro i
      ext
      simp [hu]
    rw [←cmp,LinearMap.ker_comp,LinearEquiv.ker,Submodule.comap_bot]

/-- A named anchor may be chosen independently in every occupied row. The kernel of the
linear combination map for the resulting differences is a complete invariant of the labelled
configuration under one linear change of coordinates and arbitrary row translations. -/
theorem anchored_rows_iff {J : I → Type*} (anchor : ∀ i,J i)
    (a b : ∀ i,J i → H) :
    (∃ (u : H ≃ₗ[F] H) (t : I → H),∀ i j,u (a i j)+t i=b i j) ↔
      LinearMap.ker (Finsupp.linearCombination F (fun z : (i : I) × J i =>
        a z.1 z.2-a z.1 (anchor z.1)))=
      LinearMap.ker (Finsupp.linearCombination F (fun z : (i : I) × J i =>
        b z.1 z.2-b z.1 (anchor z.1))) := by
  rw [tuple_ker_iff]
  constructor
  · rintro ⟨u,t,h⟩
    refine ⟨u,fun ⟨i,j⟩ => ?_⟩
    simp only [map_sub]
    rw [←h i j,←h i (anchor i)]
    abel
  · rintro ⟨u,h⟩
    refine ⟨u,fun i => b i (anchor i)-u (a i (anchor i)),fun i j => ?_⟩
    have eq := h ⟨i,j⟩
    dsimp only at eq
    rw [map_sub] at eq
    abel_nf at eq ⊢
    linear_combination (norm := abel) eq

/-- Pair differences give the same test without requiring an anchor, even in empty rows. -/
theorem row_pairs_iff {J : I → Type*} (a b : ∀ i,J i → H) :
    (∃ (u : H ≃ₗ[F] H) (t : I → H),∀ i j,u (a i j)+t i=b i j) ↔
      LinearMap.ker (Finsupp.linearCombination F (fun z : (i : I) × J i × J i =>
        a z.1 z.2.1-a z.1 z.2.2))=
      LinearMap.ker (Finsupp.linearCombination F (fun z : (i : I) × J i × J i =>
        b z.1 z.2.1-b z.1 z.2.2)) := by
  classical
  rw [tuple_ker_iff]
  constructor
  · rintro ⟨u,t,h⟩
    refine ⟨u,fun ⟨i,j,k⟩ => ?_⟩
    simp only [map_sub]
    rw [←h i j,←h i k]
    abel
  · rintro ⟨u,h⟩
    refine ⟨u,fun i => if hi : Nonempty (J i) then b i hi.some-u (a i hi.some) else 0,fun i j => ?_⟩
    have hi : Nonempty (J i) := ⟨j⟩
    simp only [dif_pos hi]
    have eq := h ⟨i,j,hi.some⟩
    dsimp only at eq
    rw [map_sub] at eq
    abel_nf at eq ⊢
    linear_combination (norm := abel) eq

private theorem injective_preserves_ker {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {J : Type*} (f : V →ₗ[F] W)
    (inj : Function.Injective f) (a : J → V) :
    LinearMap.ker (Finsupp.linearCombination F (fun j => f (a j))) =
      LinearMap.ker (Finsupp.linearCombination F a) := by
  have cmp : f.comp (Finsupp.linearCombination F a)=Finsupp.linearCombination F (fun j => f (a j)) := by
    apply Finsupp.lhom_ext'
    intro i
    ext
    simp
  rw [←cmp,LinearMap.ker_comp,LinearMap.ker_eq_bot.mpr inj,Submodule.comap_bot]

/-- Enlarging the fibre space never identifies two previously distinct labelled configurations. -/
theorem row_embedding_iff {J : I → Type*} {K : Type*} [AddCommGroup K] [Module F K]
    [FiniteDimensional F K] (f : H →ₗ[F] K) (inj : Function.Injective f) (a b : ∀ i,J i → H) :
    (∃ (u : K ≃ₗ[F] K) (t : I → K),∀ i j,u (f (a i j))+t i=f (b i j)) ↔
    (∃ (v : H ≃ₗ[F] H) (c : I → H),∀ i j,v (a i j)+c i=b i j) := by
  rw [row_pairs_iff (fun i j => f (a i j)) (fun i j => f (b i j)),row_pairs_iff a b]
  simp only [← map_sub,injective_preserves_ker f inj]

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.tuple_ker_iff
#print axioms Green51FrameIsomorphisms.anchored_rows_iff

#print axioms Green51FrameIsomorphisms.row_pairs_iff
#print axioms Green51FrameIsomorphisms.row_embedding_iff
