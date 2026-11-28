import Green51BCHFlatDimensions
/-! # Scalar components of the binary pair bracket -/

open Green51BCHCompression Green51BCHOptimality Finset
namespace Green51GoldForms
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

/-- The absolute trace tests membership in the Artin–Schreier image. -/
theorem absolute_trace_test :
    (∀ z : K, Algebra.trace F K (z^2) = Algebra.trace F K z) ∧
      ∀ z : K, Algebra.trace F K z=0 ↔ ∃ y : K, y^2+y=z := by
  have sq (z : K) : Algebra.trace F K (z^2) = Algebra.trace F K z := by
    simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,ZMod.card] using
      Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic F K) z
  refine ⟨sq, ?_⟩
  let A := artinSchreier (K := K)
  let T := Algebra.trace F K
  have sub : A.range ≤ T.ker := by
    rintro _ ⟨y,rfl⟩
    change Algebra.trace F K (y^2+y)=0
    rw [map_add,sq,CharTwo.add_self_eq_zero]
  have full : T.range=⊤ := LinearMap.range_eq_top.mpr (Algebra.trace_surjective F K)
  have first := A.finrank_range_add_finrank_ker
  have second := T.finrank_range_add_finrank_ker
  rw [show A.ker=Submodule.span F {(1:K)} from artinSchreier_ker,
    finrank_span_singleton one_ne_zero] at first
  rw [full,finrank_top,Module.finrank_self] at second
  have same := Submodule.eq_of_le_of_finrank_le sub (by omega)
  intro z
  change z∈T.ker ↔ z∈A.range
  rw [same]

/-- The absolute trace functional is invariant under squaring and tests the Artin–Schreier image. -/
theorem trace_functional : ∃ Q : K →ₗ[F] F, Q≠0 ∧
    (∀ x, Q (x^2)=Q x) ∧ (∀ x, Q x=0 ↔ ∃ y:K, y^2+y=x) :=
  ⟨Algebra.trace F K, Algebra.trace_ne_zero F K, absolute_trace_test⟩

/-- Two trace coordinates of a single field element. -/
def twoTraces (Q : K →ₗ[F] F) (a b : K) : K →ₗ[F] F×F :=
  (Q.comp (LinearMap.mulLeft F a)).prod (Q.comp (LinearMap.mulLeft F b))

omit [CharP K 2] [Fintype K] in
private theorem detect (Q : K →ₗ[F] F) (nq : Q≠0) (z : K)
    (all : ∀ y, Q (z*y)=0) : z=0 := by
  by_contra nz
  apply nq
  ext x
  have h := all (z⁻¹*x)
  simpa [←mul_assoc,nz] using h

omit [CharP K 2] in
/-- Multiplying inside any nonzero linear character gives the full dual space. -/
theorem represent (Q : K →ₗ[F] F) (nq : Q≠0) (l : K →ₗ[F] F) :
    ∃ c : K, ∀ x, l x=Q (c*x) := by
  let T := (Algebra.lmul F K).toLinearMap.compr₂ Q
  have inj : Function.Injective T := (injective_iff_map_eq_zero T).mpr (fun z h =>
    detect Q nq z (fun x => LinearMap.congr_fun h x))
  have dim : Module.finrank F K=Module.finrank F (K →ₗ[F] F) := by
    rw [Module.finrank_linearMap F F,Module.finrank_self,mul_one]
  obtain ⟨c,h⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp inj l
  exact ⟨c,fun x => (LinearMap.congr_fun h x).symm⟩

/-- Polar form of the scalar cubic given by the trace of `c * x³`. -/
def bracketForm (Q : K →ₗ[F] F) (c : K) : LinearMap.BilinForm F K :=
  LinearMap.mk₂ F (fun x y => Q (c*bracket x y))
    (fun x y z => by
      rw [←map_add,←mul_add]
      congr 2
      unfold bracket;ring_nf;reduce_mod_char!)
    (fun r x y => by rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp [bracket])
    (fun x y z => by
      rw [←map_add,←mul_add]
      congr 2
      unfold bracket;ring_nf;reduce_mod_char!)
    (fun r x y => by rcases (show ∀ i:F,i=0 ∨ i=1 from by decide) r with rfl|rfl <;> simp [bracket])

omit [Fintype K] in
/-- Frobenius invariance expresses a bracket evaluation as a scalar trace against a square. -/
theorem bracketForm_apply_squared (Q : K →ₗ[F] F) (sq : ∀ z, Q (z^2) = Q z) (c x y : K) :
    bracketForm Q c x y = Q ((c^2*x^4+c*x)*y^2) := by
  change Q (c*bracket x y)=_
  rw [show c*bracket x y=(c*x^2*y)+(c*x*y^2) by unfold bracket;ring,map_add,←sq (c*x^2*y),←map_add]
  congr 1;ring


/-- The polar radical is the kernel of an explicit linearized quartic. -/
theorem radical (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (c x : K) : x∈(bracketForm Q c).ker ↔ c^2*x^4+c*x=0 := by
  have eval := bracketForm_apply_squared Q sq c x
  constructor
  · intro hx
    apply detect Q nq
    intro z
    obtain ⟨y,hy⟩ := (frobeniusEquiv K 2).surjective z
    change y^2=z at hy
    rw [←hy,←eval]
    exact LinearMap.congr_fun (show bracketForm Q c x=0 from hx) y
  · intro h
    apply LinearMap.ext
    intro y
    rw [eval,h,zero_mul,map_zero];rfl

theorem radical_bound (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {c : K} (nc : c≠0) : Module.finrank F (bracketForm Q c).ker≤2 := by
  classical
  let B := bracketForm Q c
  let D := B.ker
  let _ := Fintype.ofFinite D
  let Z := univ.image (fun u:D => (u:K))
  let P : Polynomial K := Polynomial.X^4-Polynomial.C c⁻¹*Polynomial.X
  have degree : P.natDegree=4 := by
    dsimp only [P]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp [nc]),Polynomial.natDegree_X_pow]
  have non : P≠0 := by intro eq;rw [eq,Polynomial.natDegree_zero] at degree;omega
  have bound := Polynomial.card_le_degree_of_subset_roots (p:=P) (Z:=Z) (by
    intro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    apply (Polynomial.mem_roots non).mpr
    change P.eval v.val=0
    have h := (radical Q nq sq c v.val).mp v.property
    have eq := CharTwo.add_eq_zero.mp h
    simp only [P,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
    apply sub_eq_zero.mpr
    field_simp [nc] at ⊢
    exact mul_left_cancel₀ nc (by linear_combination eq))
  rw [degree,card_image_of_injective _ Subtype.val_injective,card_univ,Module.card_eq_pow_finrank (K:=F),ZMod.card] at bound
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (show 2^Module.finrank F D≤2^2 from bound)


/-- A nonzero scalar bracket can vanish on a space of dimension at most half the field dimension plus one. -/
theorem isotropic_bound (l : K →ₗ[F] F) (nl : l≠0) (A : Submodule F K)
    (zero : ∀ x∈A,∀ y∈A,l (bracket x y)=0) : 2*Module.finrank F A≤Module.finrank F K+2 := by
  obtain ⟨Q,nq,sq,_⟩ := trace_functional (K:=K)
  obtain ⟨c,rep⟩ := represent Q nq l
  have nc : c≠0 := by
    intro eq
    apply nl
    ext x
    simp [rep x,eq]
  let B := bracketForm Q c
  have iso : A≤B.orthogonal A := by
    intro y hy x hx
    exact (rep _).symm.trans (zero x hx y hy)
  have le := Submodule.finrank_mono iso
  have sz := B.finrank_add_finrank_orthogonal' A
  have inf := Submodule.finrank_mono (show A ⊓ B.ker ≤ B.ker from inf_le_right)
  have rb : Module.finrank F B.ker≤2 := radical_bound Q nq sq nc
  omega

open Green51BCH
open scoped Pointwise
/-- Every nonzero seventh-coordinate projection bounds the doubled curve's
affine dimension by half the field dimension plus one, above dimension two. -/
theorem half_bound {H : Type*} [AddCommGroup H] [Module F H] (L : K →ₗ[F] H) (nL : L≠0)
    (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p+ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (big : 3≤Module.finrank F W) : 2*Module.finrank F W≤Module.finrank F K+2 := by
  obtain ⟨t,nt,A,dim,_,kill⟩ := Green51BracketRank.trace_space_of_flat L p W inside big
  have non : ∃ u,L u≠0 := by contrapose! nL;ext x;exact nL x
  obtain ⟨u,nu⟩ := non
  obtain ⟨g,val⟩ := Module.Projective.exists_dual_eq_one F nu
  let l' := (g.comp L).comp (LinearMap.mulLeft F (t^7))
  have nl' : l'≠0 := by
    intro h
    have z := LinearMap.congr_fun h ((t^7)⁻¹*u)
    change g (L (t^7*((t^7)⁻¹*u)))=0 at z
    simp [nt,val] at z
  rw [←dim]
  exact isotropic_bound l' nl' A (fun x hx y hy => by
    change g (L (t^7*bracket x y))=0
    rw [kill x hx y hy,map_zero])


/-- A nonzero vector lies in the radical exactly when it satisfies this cubic equation. -/
theorem radical_cube_iff (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {b r : K} (nb : b≠0) (nr : r≠0) : r∈(bracketForm Q b).ker ↔ b*r^3=1 := by
  rw [radical Q nq sq]
  rw [show b^2*r^4+b*r=(b*r)*(b*r^3+1) from by ring,mul_eq_zero]
  simp only [mul_ne_zero nb nr,false_or,CharTwo.add_eq_zero]

end Green51GoldForms
#print axioms Green51GoldForms.absolute_trace_test
#print axioms Green51GoldForms.radical_cube_iff
#print axioms Green51GoldForms.trace_functional
#print axioms Green51GoldForms.represent
#print axioms Green51GoldForms.bracketForm_apply_squared
#print axioms Green51GoldForms.radical
#print axioms Green51GoldForms.radical_bound
#print axioms Green51GoldForms.isotropic_bound
#print axioms Green51GoldForms.half_bound
