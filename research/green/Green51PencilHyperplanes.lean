import Green51TwoAlternating

/-! # Extending a common isotropic space inside a specified hyperplane -/

namespace Green51PencilHyperplanes
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
private theorem orthogonal_sup (B : LinearMap.BilinForm F V) (alt : B.IsAlt) (P R : Submodule F V)
    (hP : P ≤ B.orthogonal P) (hR : R ≤ B.orthogonal R) (cross : R ≤ B.orthogonal P) :
    P ⊔ R ≤ B.orthogonal (P ⊔ R) := by
  intro x hx y hy
  obtain ⟨p,hp,r,hr,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨q,hq,s,hs,rfl⟩ := Submodule.mem_sup.mp hy
  change B (q+s) (p+r)=0
  simp only [map_add,LinearMap.add_apply]
  rw [hP hp q hq,hR hr s hs,cross hr q hq,alt.isRefl p s (cross hs p hp)]
  simp

/-- Extend a common isotropic space inside a hyperplane using its intersection with the first radical. -/
theorem of_radical_dimension (A B : LinearMap.BilinForm F V) (altA : A.IsAlt) (altB : B.IsAlt)
    {k : ℕ}
    (D : Submodule F V) (small : Module.finrank F D≤k+1)
    (room : 2*k+2≤Module.finrank F V + Module.finrank F (D ⊓ A.ker : Submodule F V))
    (D0 : D≤A.orthogonal D) (D1 : D≤B.orthogonal D)
    (cross : A.orthogonal D≤B.orthogonal D) (l : V →ₗ[F] F) (zero : D≤l.ker) :
    ∃ U : Submodule F V, D≤U ∧ U≤l.ker ∧ Module.finrank F U=k+1 ∧
      U≤A.orthogonal U ∧ U≤B.orthogonal U := by
  by_cases eq : Module.finrank F D=k+1
  · exact ⟨D,le_rfl,zero,eq,D0,D1⟩
  let r:=Module.finrank F D
  obtain ⟨X,comp⟩:=D.exists_isCompl
  let P:=A.orthogonal D ⊓ X
  let N:=P ⊓ l.ker
  have room : 2*(k-r)+1 ≤ Module.finrank F N := by
    have dx:=Submodule.finrank_add_eq_of_isCompl comp
    have orth:=A.finrank_add_finrank_orthogonal' D
    have DP:=(A.orthogonal D).finrank_sup_add_finrank_inf_eq X
    have DP' := Submodule.finrank_le (A.orthogonal D ⊔ X)
    have ker:=l.finrank_range_add_finrank_ker
    have rk := Submodule.finrank_le l.range
    rw [Module.finrank_self] at rk
    have DN:=P.finrank_sup_add_finrank_inf_eq l.ker
    have DN':=Submodule.finrank_le (P ⊔ l.ker)
    dsimp only [P,N,r] at *
    omega
  obtain ⟨e,inj⟩:=finrank_le_iff_exists_linearMap.mp (show
    Module.finrank F (Fin (2*(k-r)+1) → F) ≤ Module.finrank F N by simpa using room)
  let f:=N.subtype.comp e
  let E:=f.range
  have dimE : Module.finrank F E=2*(k-r)+1 := by
    rw [show E=f.range from rfl,f.finrank_range_of_inj (N.subtype_injective.comp inj)]
    simp
  obtain ⟨T,dimT,tA,tB⟩:=Green51TwoAlternating.simultaneous F (k-r) (A.restrict E) (B.restrict E)
    (fun x => altA x.val) (fun x => altB x.val) dimE
  let R:=T.map E.subtype
  have dimR : Module.finrank F R=k-r+1 := (E.finrank_map_subtype_eq T).trans dimT
  have incl : R≤N := by
    rintro _ ⟨x,_,rfl⟩
    obtain ⟨u,hu⟩:=x.property
    change (x : V) ∈ N
    rw [←hu]
    exact (e u).property
  have ox : R≤X := fun x hx => (incl hx).1.2
  have oa : R≤A.orthogonal D := fun x hx => (incl hx).1.1
  have disj:=comp.disjoint.mono_right ox
  have dimU:=D.finrank_sup_add_finrank_inf_eq R
  rw [disj.eq_bot,finrank_bot] at dimU
  have ownA : R≤A.orthogonal R := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact tA y hy x hx
  have ownB : R≤B.orthogonal R := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact tB y hy x hx
  refine ⟨D⊔R,le_sup_left,sup_le zero (fun x hx => (incl hx).2),?_,
    orthogonal_sup A altA D R D0 ownA oa,orthogonal_sup B altB D R D1 ownB (oa.trans cross)⟩
  dsimp only [r] at dimR
  omega
/-- Given a common isotropic space whose first orthogonal annihilates both forms
and whose intersection with the first radical is nontrivial, any containing
hyperplane contains a common isotropic subspace of half-rounded-up dimension. -/
theorem in_hyperplane (A B : LinearMap.BilinForm F V) (altA : A.IsAlt) (altB : B.IsAlt)
    {k : ℕ} (dimension : Module.finrank F V=2*k+1)
    (D : Submodule F V) (small : Module.finrank F D≤k+1)
    (rad : 1≤Module.finrank F (D ⊓ A.ker : Submodule F V))
    (D0 : D≤A.orthogonal D) (D1 : D≤B.orthogonal D)
    (cross : A.orthogonal D≤B.orthogonal D) (l : V →ₗ[F] F) (zero : D≤l.ker) :
    ∃ U : Submodule F V, D≤U ∧ U≤l.ker ∧ Module.finrank F U=k+1 ∧
      U≤A.orthogonal U ∧ U≤B.orthogonal U :=
  of_radical_dimension A B altA altB D small (by omega) D0 D1 cross l zero

end Green51PencilHyperplanes
#print axioms Green51PencilHyperplanes.of_radical_dimension
#print axioms Green51PencilHyperplanes.in_hyperplane
