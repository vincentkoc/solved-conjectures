import Green51FirstSeparation
import Green51PairedTypes

/-! # Sixteen-label relations in eleven binary dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51ElevenRelations
local notation "F" => ZMod 2

/-- A zero-sum set of sixteen labels in eleven dimensions already forces
an affine three-space in its double. -/
theorem affine_of_sixteen_sum (A : Finset (Cube 11)) (size : A.card=16)
    (sum : (∑ a∈A,a)=0) : ∃p, FlatAt A p := by
  by_cases linear : FlatAt A 0
  · exact ⟨0,linear⟩
  have free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ a∈T,a)≠0 :=
    fun T sub sz zero => linear ((flat_zero A).mpr
      ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,sz,zero⟩))
  obtain ⟨P,eval,parity,kernel,_⟩ := Green51SparseDimensions.even_pair_columns A free
  have distance (x:P.ker) (non:x≠0) : 8≤(supp x.val).card := by
    have even := parity x.val x.property
    by_contra! low
    exact non (Subtype.ext (kernel x.val (by omega) x.property))
  have rank : 4≤Module.finrank F P.ker := by
    have eq := P.finrank_range_add_finrank_ker
    have up := Submodule.finrank_le P.range
    rw [show Module.finrank F (Cube A.card)=16 by simp [Cube,size]] at eq
    rw [show Module.finrank F (F×Cube 11)=12 by simp [Module.finrank_prod,Cube]] at up
    omega
  have ones : (fun _=>1)∈P.ker := by
    change P (fun _=>1)=0
    have full : supp (fun _:Fin A.card => (1:F))=univ := by ext i; simp [supp]
    rw [eval,full]
    apply Prod.ext
    · simp only [Prod.fst_sum,Prod.fst_zero,sum_const,card_univ,Fintype.card_fin,size]; decide
    · simp only [Prod.snd_sum,Prod.snd_zero]
      exact (A.equivFin.symm.sum_comp Subtype.val).trans ((sum_attach A id).trans sum)
  obtain ⟨p,count,planes⟩ :=
    Green51Hadamard.partition_of_ones size P.ker rank ones distance
  obtain ⟨W,dim,inside⟩ := Green51FirstSeparation.partition_flat A P eval distance p count planes
  exact ⟨_,W,dim,fun _ ⟨w,hw,eq⟩ => eq ▸ inside w hw⟩

end Green51ElevenRelations
#print axioms Green51ElevenRelations.affine_of_sixteen_sum
