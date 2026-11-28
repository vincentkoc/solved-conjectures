import Green51BCHInverse
import Green51LocalFlats

/-! # The largest affine subspace in the double of a set of BCH columns -/

open Green51LocalFlats Green51SparseBounds
open scoped Pointwise
namespace Green51BCH
variable {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K] [Finite K]
local notation "F" => ZMod 2
/-- The largest flat in the double of a set of at least three BCH columns. -/
theorem coset_dimension (S : Set K) (three : 3 ≤ S.ncard) :
    maxCosetDim F (Space K) (curve '' S+curve '' S) = max 2 (maxCosetDim F K S-1) := by
  classical
  let _ := Fintype.ofFinite K
  let A := (curve '' S).toFinset
  have count : A.card=S.ncard := by
    rw [show A=(curve '' S).toFinset from rfl,←Set.ncard_eq_toFinset_card']
    apply Set.ncard_image_of_injective
    exact fun _ _ eq => congrArg Prod.fst eq
  have plane := plane_of_three A (count ▸ three)
  obtain ⟨U,du,incl⟩ := plane
  have two : 2 ≤ maxCosetDim F (Space K) (curve '' S+curve '' S) := by
    apply (le_iff_coset (by decide) _).mpr
    refine ⟨U,0,du,?_⟩
    rw [zero_vadd]
    intro z hz
    have h : z ∈ (↑(A+A) : Set (Space K)) := incl z hz
    simpa only [Finset.coe_add,A,Set.coe_toFinset] using h
  have threshold (d : ℕ) (hd : 3≤d) :
      d ≤ maxCosetDim F (Space K) (curve '' S+curve '' S) ↔ d+1 ≤ maxCosetDim F K S := by
    rw [le_iff_coset (by omega : 0<d),le_iff_coset (by omega : 0<d+1)]
    constructor
    · rintro ⟨W,p,rank,sub⟩
      obtain ⟨x,U,dimen,inside⟩ := (subset_inverse hd S).mp ⟨p,W,rank,sub⟩
      exact ⟨U,x,dimen,inside⟩
    · rintro ⟨U,x,rank,sub⟩
      obtain ⟨p,W,dimen,inside⟩ := (subset_inverse hd S).mpr ⟨x,U,rank,sub⟩
      exact ⟨W,p,dimen,inside⟩
  by_contra notEq
  by_cases gt : maxCosetDim F (Space K) (curve '' S+curve '' S) > max 2 (maxCosetDim F K S-1)
  · have h := (threshold _ (by omega)).mp (le_refl (maxCosetDim F (Space K) (curve '' S+curve '' S)))
    omega
  · have h := (threshold (maxCosetDim F K S-1) (by omega)).mpr (by omega)
    omega
/-- The full curve over a field of binary dimension at least four has
largest affine flat of dimension exactly one less than the field. -/
theorem full_dimension (dim : 4 ≤ Module.finrank F K) :
    maxCosetDim F (Space K) (Set.range (curve (K:=K)) + Set.range curve) =
      Module.finrank F K-1 := by
  let _ := Fintype.ofFinite K
  have card : 3 ≤ (Set.univ : Set K).ncard := by
    rw [Set.ncard_univ,Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=F),ZMod.card]
    have bound := Nat.pow_le_pow_right (by decide : 0<2) dim
    omega
  have eq := coset_dimension (Set.univ : Set K) card
  rwa [Set.image_univ,maxCosetDim_univ,max_eq_right (by omega)] at eq

end Green51BCH
#print axioms Green51BCH.coset_dimension
#print axioms Green51BCH.full_dimension
