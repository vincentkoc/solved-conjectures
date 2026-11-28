import Green51PencilHyperplanes
/-! # The span of chains for a pair of symmetric forms -/
namespace Green51PencilChains
variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]

def chainSpace (k : ℕ) (c : I → ℕ → V) : Submodule F V :=
  Submodule.span F (Set.range fun x : I × Fin (k+1) => c x.1 x.2.val)

theorem generators (k : ℕ) (c : I → ℕ → V) (i : I) (j : ℕ) (hj : j≤k) :
    c i j ∈ chainSpace (F:=F) k c :=
  Submodule.subset_span ⟨(i,⟨j,by omega⟩),rfl⟩

theorem orthogonals (A B : LinearMap.BilinForm F V) (k : ℕ) (c : I → ℕ → V)
    (symA : ∀ x y,A x y=A y x) (symB : ∀ x y,B x y=B y x)
    (start : ∀ i x,A (c i 0) x=0)
    (step : ∀ i j,j<k → ∀ x,A (c i (j+1)) x=B (c i j) x)
    (last : ∀ i x,B (c i k) x=0) :
    let D := chainSpace (F:=F) k c
    D≤A.orthogonal D ∧ D≤B.orthogonal D ∧ A.orthogonal D≤B.orthogonal D := by
  intro D
  have cross : A.orthogonal D ≤ B.orthogonal D := by
    intro x hx
    have d : D≤(B.flip x).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,j⟩,rfl⟩
      change B (c i j.val) x=0
      by_cases eq : j.val=k
      · rw [eq,last]
      · rw [←step i j.val (by omega)];exact hx _ (generators k c i _ (by omega))
    exact fun _ hy => d hy
  have orth (i : I) (a : ℕ) (ha : a≤k) : c i a ∈ A.orthogonal D := by
    induction a with
    | zero => exact fun x _ => (symA _ _).trans (start i x)
    | succ a ih =>
      have prev := cross (ih (by omega))
      intro x hx
      change A x (c i (a+1))=0
      rw [symA,step i a (by omega),symB];exact prev x hx
  have own : D ≤ A.orthogonal D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact orth i j.val (by omega)
  exact ⟨own,own.trans cross,cross⟩

theorem forced (A B : LinearMap.BilinForm F V) (k : ℕ) (c : I → ℕ → V)
    (symA : ∀ x y,A x y=A y x) (symB : ∀ x y,B x y=B y x)
    (start : ∀ i x,A (c i 0) x=0)
    (step : ∀ i j,j<k → ∀ x,A (c i (j+1)) x=B (c i j) x)
    (U : Submodule F V) (self : U=A.orthogonal U) (iso : U≤B.orthogonal U) :
    chainSpace (F:=F) k c ≤ U := by
  have one (i : I) (j : ℕ) (hj : j≤k) : c i j∈U := by
    induction j with
    | zero => rw [self];exact fun x _ => (symA _ _).trans (start i x)
    | succ j ih =>
      have prev := iso (ih (by omega))
      rw [self]
      intro x hx
      change A x (c i (j+1))=0
      rw [symA,step i j (by omega),symB];exact prev x hx
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i,j⟩,rfl⟩
  exact one i j.val (by omega)
end Green51PencilChains
#print axioms Green51PencilChains.orthogonals
#print axioms Green51PencilChains.forced
