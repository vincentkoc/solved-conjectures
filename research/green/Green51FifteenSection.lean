import Green51AffineColumnRelations
import Green51SparseDimensions

/-! # Fifteen binary labels in dimension ten -/

open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51SimplexSection
local notation "F" => ZMod 2
local notation "V" => Cube 10

private theorem present {n : ℕ} (A : Finset V) (size : A.card=n)
    (free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0) :
    ∃ a : Fin n → V, univ.image a=A ∧
      ∀ z:(augmented a).ker, z≠0 → 8≤(supp z.val).card := by
  classical
  subst n
  let a (i : Fin A.card) := (A.equivFin.symm i).val
  have image : univ.image a=A := by
    ext x
    constructor
    · rintro h
      obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact (A.equivFin.symm i).property
    · intro hx
      exact mem_image.mpr ⟨A.equivFin ⟨x,hx⟩,mem_univ _,by simp [a]⟩
  obtain ⟨P,eval,parity,small,_⟩ := Green51SparseDimensions.even_pair_columns A free
  have same : augmented a=P := by
    apply LinearMap.ext
    intro z
    rw [eval]
    simp only [augmented,Fintype.linearCombination_apply,supp,sum_filter]
    apply sum_congr rfl
    intro i _
    rcases (show ∀ u:F,u=0 ∨ u=1 from by decide) (z i) with h|h <;> simp [h,a]
  refine ⟨a,image,?_⟩
  intro z nz
  have zero : P z.val=0 := (LinearMap.congr_fun same z.val).symm.trans z.property
  have h := parity _ zero
  by_contra! bad
  exact nz (Subtype.ext (small _ (by omega) zero))

private theorem kernel_card (a : Fin 15 → V) : 16≤Fintype.card (augmented a).ker := by
  let P := augmented a
  have total := P.finrank_range_add_finrank_ker
  have up := Submodule.finrank_le P.range
  rw [show Module.finrank F (Cube 15)=15 by simp [Cube]] at total
  rw [show Module.finrank F (F×V)=11 by simp [Module.finrank_prod,Cube]] at up
  have lower : 4≤Module.finrank F P.ker := by omega
  rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
  exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) lower

/-- Every fifteen-point configuration in the binary ten-space with no
four- or six-point zero sum is in the same affine orbit. -/
theorem affine_unique (A B : Finset V) (aSize : A.card=15) (bSize : B.card=15)
    (aFree : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0)
    (bFree : ∀ T⊆B, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0) :
    ∃ (g : V ≃ₗ[F] V) (t : V), A.image (fun x => g x+t)=B := by
  classical
  obtain ⟨a,ha,ad⟩ := present A aSize aFree
  obtain ⟨b,hb,bd⟩ := present B bSize bFree
  obtain ⟨σ,hs⟩ := simplex_permutation (augmented a).ker (augmented b).ker
    (kernel_card a) (kernel_card b) (fun z nz => by have := ad z nz; omega)
    (fun z nz => by have := bd z nz; omega)
  have ker : (augmented a).ker=(augmented (fun i => b (σ.symm i))).ker := by
    ext z
    change augmented a z=0 ↔ augmented (fun i => b (σ.symm i)) z=0
    rw [augmented_reindex]
    exact hs z
  obtain ⟨g,t,map⟩ := affine_of_relations 0 a _ ker
  refine ⟨g,t,?_⟩
  rw [←ha,←hb,image_image]
  ext x
  simp only [mem_image,mem_univ,true_and,Function.comp_apply]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨σ.symm i,(map i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨σ i,by simpa using map (σ i)⟩

end Green51SimplexSection
#print axioms Green51SimplexSection.affine_unique
