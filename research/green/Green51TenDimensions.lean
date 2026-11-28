import Green51AffineMatchings

/-! # The smallest ambient dimension separating linear and affine three-spaces -/

open Finset Green50Downsets Green51SparseDimensions Green51AffineMatchings
open scoped Classical Pointwise
namespace Green51TenDimensions
local notation "F" => ZMod 2
variable {G H : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [DecidableEq H]

private def FlatAt (A : Finset G) (p : G) : Prop :=
  ∃ W : Submodule F G, Module.finrank F W=3 ∧ p +ᵥ (W : Set G) ⊆ ↑(A+A)

private theorem center {A : Finset G} {p : G} (h : FlatAt A p) : p∈A+A := by
  obtain ⟨W,_,sub⟩ := h
  exact sub ⟨0,W.zero_mem,add_zero p⟩

private theorem flat_zero (A : Finset G) :
    FlatAt A 0 ↔ ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  simp only [FlatAt,zero_vadd]
  rfl

private theorem image_double (f : G →ₗ[F] H) (A : Finset G) :
    A.image f+A.image f=(A+A).image f := by
  rw [image_add]

private theorem flat_image (f : G →ₗ[F] H) (inj : Function.Injective f) (A : Finset G) (p : G) :
    FlatAt (A.image f) (f p) ↔ FlatAt A p := by
  constructor
  · rintro ⟨V,dim,sub⟩
    have range : V≤f.range := by
      intro v hv
      have h : f p+v∈A.image f+A.image f := sub ⟨v,hv,rfl⟩
      rw [image_double] at h
      obtain ⟨a,_,eq⟩ := mem_image.mp h
      exact ⟨a-p,by rw [map_sub,eq]; abel⟩
    let W := V.comap f
    have eq : W.map f=V := Submodule.map_comap_eq_self range
    refine ⟨W,(W.equivMapOfInjective f inj).finrank_eq.trans (eq ▸ dim),?_⟩
    rintro _ ⟨w,hw,rfl⟩
    have h : f p+f w∈A.image f+A.image f := sub ⟨f w,hw,rfl⟩
    rw [image_double,←map_add] at h
    obtain ⟨a,ha,m⟩ := mem_image.mp h
    change p+w∈A+A
    exact inj m ▸ ha
  · rintro ⟨W,dim,sub⟩
    refine ⟨W.map f,(W.equivMapOfInjective f inj).finrank_eq.symm.trans dim,?_⟩
    rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
    change f p+f w∈A.image f+A.image f
    rw [image_double,←map_add]
    exact mem_image_of_mem _ (sub ⟨w,hw,rfl⟩)

private theorem separates_image (f : G →ₗ[F] H) (inj : Function.Injective f) (A : Finset G) :
    ((¬FlatAt (A.image f) 0) ∧ ∃ p,FlatAt (A.image f) p) ↔
      ((¬FlatAt A 0) ∧ ∃ p,FlatAt A p) := by
  have lin := flat_image f inj A 0
  rw [map_zero] at lin
  rw [lin]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · rintro ⟨y,h⟩
    have mem := center h
    rw [image_double] at mem
    obtain ⟨x,_,rfl⟩ := mem_image.mp mem
    exact ⟨x,(flat_image f inj A x).mp h⟩
  · rintro ⟨x,h⟩; exact ⟨f x,(flat_image f inj A x).mpr h⟩

private theorem field_example (n : ℕ) (large : 10≤n) :
    ∃ A : Finset (Cube n), A.card=16 ∧ (¬FlatAt A 0) ∧ ∃ p,FlatAt A p := by
  classical
  let K := GaloisField 2 4
  let : Fintype K := Fintype.ofFinite K
  have size : Fintype.card K=16 := by
    rw [←Nat.card_eq_fintype_card]; exact GaloisField.card 2 4 (by decide)
  have dim : Module.finrank F K=4 := GaloisField.finrank 2 (by decide)
  let fixed : Submodule F K :=
    { carrier := {x | x^4=x}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change (x+y)^(2*2)=x+y
        rw [pow_mul,CharTwo.add_sq,CharTwo.add_sq]
        change x^4=x at hx
        change y^4=y at hy
        simpa only [←pow_mul] using congrArg₂ (·+·) hx hy
      smul_mem' := by
        intro c x hx
        rcases (show ∀ u:F,u=0 ∨ u=1 from by decide) c with rfl|rfl <;> simp_all }
  have fixdim : Module.finrank F fixed≤2 := by
    let p : Polynomial K := Polynomial.X^4-Polynomial.X
    have deg : p.natDegree=4 := by
      rw [show p=Polynomial.X^4-Polynomial.X by rfl,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
      simp
    have nz : p≠0 := fun h => by simp [h] at deg
    have sub : univ.image (fun z : fixed => z.val) ⊆ p.roots.toFinset := by
      intro z hz
      obtain ⟨y,_,rfl⟩ := mem_image.mp hz
      rw [Multiset.mem_toFinset,Polynomial.mem_roots nz]
      simpa [Polynomial.IsRoot,p] using sub_eq_zero.mpr y.property
    have le := (card_le_card sub).trans (p.roots.toFinset_card_le.trans p.card_roots')
    rw [card_image_of_injective _ Subtype.val_injective,card_univ,Module.card_eq_pow_finrank (K:=F),ZMod.card,deg] at le
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp le
  have fifth (x : K) : x^5∈fixed := by
    change (x^5)^4=x^5
    have h := FiniteField.pow_card x
    rw [size] at h
    calc
      _ = x^16*x^4 := by ring
      _ = x^5 := by rw [h];ring
  let V := K × K × fixed
  let f : V →ₗ[F] (Fin 3 → K) :=
    { toFun := fun a => ![a.1,a.2.1,a.2.2.val]
      map_add' := by intro a b; funext i;fin_cases i <;> rfl
      map_smul' := by intro c a; funext i;fin_cases i <;> rfl }
  have inj : Function.Injective f := by
    intro a b h
    exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (Subtype.ext (congrFun h 2)))
  let small (x : K) : V := (x,x^3,⟨x^5,fifth x⟩)
  let A := univ.image small
  have eq : A.image f=univ.image (Green51AffineSeparation.graphPoint (K:=K)) := by
    dsimp only [A]; rw [image_image]
    apply image_congr; intro x _
    funext i; fin_cases i <;> simp [f,small,Green51AffineSeparation.graphPoint,Green50BCH.column]
  have witness : (¬FlatAt A 0) ∧ ∃ p,FlatAt A p := by
    apply (separates_image f inj A).mp
    rw [eq,flat_zero]
    refine ⟨Green51AffineSeparation.graph_linear_avoidance (by omega),?_⟩
    obtain ⟨W,p,rank,inside⟩ := Green51AffineSeparation.graph_derivative_flat (K:=K)
    exact ⟨p,W,by omega,inside⟩
  have fits : Module.finrank F V≤Module.finrank F (Cube n) := by
    simp only [V,Module.finrank_prod,dim,Cube,Module.finrank_pi,Fintype.card_fin]
    omega
  obtain ⟨j,ji⟩ := finrank_le_iff_exists_linearMap.mp fits
  refine ⟨A.image j,?_,(separates_image j ji A).mpr witness⟩
  rw [card_image_of_injective _ ji,←card_image_of_injective A inj,eq,Green51AffineSeparation.graph_size,size]

private theorem packing_gap (a : ℕ) (ha : 8≤a) : a^3 < 2*a+(2*a).choose 3 := by
  have prod := Nat.descFactorial_eq_factorial_mul_choose (2*a) 3
  have eval : (2*a).descFactorial 3 = (2*a-2)*(2*a-1)*(2*a) := by
    simp [Nat.descFactorial_succ,mul_assoc]
  rw [eval,show Nat.factorial 3=6 by decide] at prod
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [show 2*(8+b)-2=14+2*b by omega,show 2*(8+b)-1=15+2*b by omega] at prod
  nlinarith [Nat.zero_le (b^2),Nat.zero_le (b^3)]

/-- Separating an affine d-flat from every linear three-space requires
ambient dimension at least 3d+1. The general construction uses 3d+3. -/
theorem ambient_cost {n d : ℕ} (dlarge : 3≤d) (A : Finset (Cube n))
    (avoid : ¬∃ V : Submodule F (Cube n), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A)
    (W : Submodule F (Cube n)) (rank : Module.finrank F W=d)
    (p : Cube n) (inside : p +ᵥ (W : Set (Cube n)) ⊆ ↑(A+A)) :
    3*d+1≤n := by
  have cost := affine_flat_cost A avoid W p inside (rank ▸ dlarge)
  rw [rank,pow_succ,mul_comm] at cost
  have eight : 8≤2^d := Nat.pow_le_pow_right (by decide : 0 < 2) dlarge
  have bound := triple_packing A (by omega) avoid
  have cube : Fintype.card (Cube n)=2^n := by simp [Cube]
  rw [cube] at bound
  have l := (packing_gap (2^d) eight).trans_le ((Nat.add_le_add cost (Nat.choose_le_choose 3 cost)).trans bound)
  rw [←pow_mul,Nat.mul_comm d 3] at l
  by_contra! h
  exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide) (show n≤3*d by omega))) l

/-- Ten is the first binary cube dimension where a double can contain an
affine three-space and avoid all linear three-spaces. Sixteen labels suffice
in every dimension from ten onwards. -/
theorem separation_iff (n : ℕ) :
    (∃ A : Finset (Cube n),
      (¬∃ V : Submodule F (Cube n), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A) ∧
      ∃ (W : Submodule F (Cube n)) (p : Cube n), Module.finrank F W=3 ∧
        p +ᵥ (W : Set (Cube n)) ⊆ ↑(A+A)) ↔ 10≤n := by
  constructor
  · rintro ⟨A,avoid,W,p,rank,inside⟩
    exact ambient_cost (by decide : 3≤3) A avoid W rank p inside
  · intro large
    obtain ⟨A,_,avoid,p,W,rank,inside⟩ := field_example n large
    exact ⟨A,fun h => avoid ((flat_zero A).mpr h),W,p,rank,inside⟩

/-- In particular both minimum budgets, sixteen labels and ten ambient
coordinates, are attained by a single set. -/
theorem sixteen_in_ten :
    ∃ A : Finset (Cube 10), A.card=16 ∧
      (¬∃ V : Submodule F (Cube 10), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A) ∧
      ∃ (W : Submodule F (Cube 10)) (p : Cube 10), Module.finrank F W=3 ∧
        p +ᵥ (W : Set (Cube 10)) ⊆ ↑(A+A) := by
  obtain ⟨A,sz,avoid,p,W,rank,inside⟩ := field_example 10 le_rfl
  exact ⟨A,sz,fun h => avoid ((flat_zero A).mpr h),W,p,rank,inside⟩

end Green51TenDimensions

#print axioms Green51TenDimensions.ambient_cost
#print axioms Green51TenDimensions.separation_iff
#print axioms Green51TenDimensions.sixteen_in_ten
