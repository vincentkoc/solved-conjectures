import Green51FourSpaceLabels
import Green51FourSpaceNormal
import Green51FourSpaceRank

/-! # First dimension separating affine four-spaces from linear three-spaces -/
open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51FourSpace
local notation "F" => ZMod 2

/-- Every sixteen-site code satisfying the affine support restrictions has dimension at most five. -/
theorem code_rank (C:Submodule F (Cube 16)) (hc:validCode C) : Module.finrank F C≤5 := by
  by_contra! big
  obtain ⟨K,hK,valid,w,hw,shape⟩:=normalized_code C hc big
  have := normalized_rank valid hw shape
  omega

variable {G:Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- A four-dimensional affine flat in the double of a set avoiding linear
three-spaces requires ambient dimension at least fifteen. -/
theorem dimension_lower (A:Finset G)
    (avoid:¬∃ V:Submodule F G,Module.finrank F V=3 ∧ ∀v∈V,v∈A+A)
    (W:Submodule F G) (t:G) (dim:Module.finrank F W=4)
    (inside:t +ᵥ (W:Set G) ⊆ ↑(A+A)) : 15≤Module.finrank F G := by
  obtain ⟨K,large,conditions⟩:=obstruction_code (by decide : 3≤4) A avoid t W dim inside
  obtain ⟨C,rank,valid⟩:=code_in_coordinates K conditions
  have small:=code_rank C valid
  norm_num at large
  omega

/-- In dimensions through fourteen, an avoiding double has coset dimension at most three. -/
theorem max_coset_bound (A:Finset G) (dim:Module.finrank F G≤14)
    (avoid:¬∃ V:Submodule F G,Module.finrank F V=3 ∧ ∀v∈V,v∈A+A) :
    maxCosetDim F G ↑(A+A)≤3 := by
  classical
  apply csSup_le
  · exact ⟨0,⊥,by simp,by simp⟩
  · rintro _ ⟨S,hS,rfl⟩
    by_contra! big
    have non : S≠⊥ := by intro h; rw [h,AffineSubspace.direction_bot] at big; simp at big
    obtain ⟨x,hx⟩:=(AffineSubspace.nonempty_iff_ne_bot S).mpr non
    have req:Module.finrank F (Cube 4)≤Module.finrank F S.direction := by simp [Cube];omega
    obtain ⟨f,inj⟩:=finrank_le_iff_exists_linearMap.mp req
    let g:=S.direction.subtype.comp f
    have ginj:Function.Injective g:=Subtype.val_injective.comp inj
    have rank:Module.finrank F g.range=4 := by rw [g.finrank_range_of_inj ginj];simp [Cube]
    have inside:x +ᵥ (g.range:Set G) ⊆ ↑(A+A) := by
      rintro _ ⟨y,⟨v,rfl⟩,rfl⟩
      apply hS
      simpa [g,vadd_eq_add,add_comm] using AffineSubspace.vadd_mem_of_mem_direction (f v).property hx
    have := dimension_lower A avoid g.range x rank inside
    omega

/-- The least possible ambient dimension is fifteen. A witness there needs only thirty-two labels. -/
theorem first_dimension :
    IsLeast {n:ℕ | ∃ A:Finset (Cube n),
        (¬∃ V:Submodule F (Cube n),Module.finrank F V=3 ∧ ∀v∈V,v∈A+A) ∧
        ∃ (W:Submodule F (Cube n)) (t:Cube n),Module.finrank F W=4 ∧ t +ᵥ (W:Set (Cube n)) ⊆ ↑(A+A)} 15 ∧
      ∃ A:Finset (Cube 15),A.card=32 ∧
        (¬∃ V:Submodule F (Cube 15),Module.finrank F V=3 ∧ ∀v∈V,v∈A+A) ∧
        ∃ (W:Submodule F (Cube 15)) (t:Cube 15),Module.finrank F W=4 ∧ t +ᵥ (W:Set (Cube 15)) ⊆ ↑(A+A) := by
  obtain ⟨A,size,avoid,inside⟩:=Green51AffineMatchings.sharp_examples 4 (by decide)
  refine ⟨⟨⟨A,avoid,inside⟩,?_⟩,A,size,avoid,inside⟩
  rintro n ⟨B,away,W,t,dim,flat⟩
  simpa [Cube] using dimension_lower B away W t dim flat

end Green51FourSpace
#print axioms Green51FourSpace.code_rank
#print axioms Green51FourSpace.dimension_lower
#print axioms Green51FourSpace.max_coset_bound
#print axioms Green51FourSpace.first_dimension
