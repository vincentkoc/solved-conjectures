import Green51OddTraceCriterion

/-! # Ratios in proper subfields always attain the larger BCH flat -/

open Green51GoldForms Green51BCHCompression
namespace Green51OddTrace
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
open Green51BCH Green51BCHOptimality Green51LocalFlats
open scoped Pointwise
open Green51PencilWindows

open Green50Downsets Green51BCHCompression Green51BCHOptimality Green52CubicPolar Green53PolynomialColours

theorem seventh_orthogonal (Q : K →ₗ[F] F) (a : K) (D : Submodule F K)
    (room : 3*Module.finrank F D < Module.finrank F K) :
    ∃ h : K,h≠0 ∧ ∀ x∈D,Q ((a*h^7)*x)=0 := by
  let M := (((Algebra.lmul F K).toLinearMap.compl₂ D.subtype).compr₂ Q).comp (LinearMap.mulLeft F a)
  let e : (D →ₗ[F] F) ≃ₗ[F] Cube (Module.finrank F D) := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_linearMap F F,Module.finrank_self,mul_one];simp [Cube])
  obtain ⟨h,nh,eq⟩:=seventh_meets_of_dimension (e.toLinearMap.comp M) room
  have van : M (h^7)=0 := (e.map_eq_zero_iff).mp eq
  exact ⟨h,nh,fun x hx => LinearMap.congr_fun van ⟨x,hx⟩⟩

/-- A proper coefficient subfield of index at least three supplies the large flat for every scalar. -/
theorem subfield_maximum {E : Type*} [Field E] [CharP E 2] [Algebra F E] [Fintype E]
    (j : E →ₐ[F] K) (b : E) (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y:K, y^2+y=z)
    {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k+1)
    (room : 3*Module.finrank F E ≤ Module.finrank F K) {a:K} (na:a≠0) :
    let L:=twoTraces Q a (a*j b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))=k+1 := by
  intro L
  rw [exact_maximum Q nQ sq test hk degree na]
  apply if_pos
  let D:=Submodule.span F (Set.range (fun i : Fin (k+1) => term k b i.val))
  let QE:=Q.comp j.toLinearMap
  have one : Q 1≠0 := by
    intro eq
    obtain ⟨x,hx⟩:=(test 1).mp eq
    have cu : x^3=1 := by
      linear_combination (norm := (ring_nf;reduce_mod_char!)) (x+1)*hx
    have eq1 := (odd_cube_bijective degree).injective
      (show x^3=(1:K)^3 from cu.trans (one_pow 3).symm)
    simp [eq1,CharTwo.add_self_eq_zero] at hx
  have nQE : QE ≠ 0 := by
    intro h; apply one
    simpa [QE] using LinearMap.congr_fun h 1
  have alt (c : K) : (bracketForm Q c).IsAlt := fun x => by
    change Q (c*bracket x x)=0
    simp [bracket,CharTwo.add_self_eq_zero]
  obtain ⟨U,dim,first,second⟩:=Green51TwoAlternating.simultaneous F k (bracketForm Q 1)
    (bracketForm Q (j b)) (alt 1) (alt (j b)) degree
  have iso (x) (hx : x∈U) (y) (hy : y∈U) : Q (bracket x y)=0 := by
    simpa [bracketForm] using first x hx y hy
  have inside : D ≤ U.comap j.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change j (term k b i.val)∈U
    rw [←term_map j]
    exact forced Q nQ sq degree (j b) _ (term_zero k (j b)) (term_step degree (j b)) U dim.ge
      iso second i.val (by omega)
  have bound := isotropic_bound QE nQE D (by
    intro x hx y hy
    have h:=iso (j x) (inside hx) (j y) (inside hy)
    simpa [QE,bracket] using h)
  have size:=(D.equivMapOfInjective j.toLinearMap j.injective).finrank_eq
  change Module.finrank F D=Module.finrank F (D.map j.toLinearMap) at size
  have small:=Submodule.finrank_le D
  obtain ⟨h,nh,zero⟩ := seventh_orthogonal Q (a^2) (D.map j.toLinearMap) (by omega)
  refine ⟨h,nh,fun i => zero _ ?_⟩
  rw [term_map j]
  exact ⟨term k b i.val,Submodule.subset_span ⟨i,rfl⟩,rfl⟩

theorem proper_subfield (E : IntermediateField F K) (proper : E≠⊤)
    {b : K} (hb : b∈E) (Q : K →ₗ[F] F) (nQ : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y:K,y^2+y=z)
    {k : ℕ} (hk : 2≤k) (degree : Module.finrank F K=2*k+1) {a:K} (na:a≠0) :
    let L:=twoTraces Q a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L)+Set.range (lifted L))=k+1 := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  have tower:=Module.finrank_mul_finrank F E K
  have big : 3≤Module.finrank E K := by
    have n1 := mt IntermediateField.finrank_eq_one_iff_eq_top.mp proper
    have pos : 0<Module.finrank E K := Module.finrank_pos
    by_contra! sm
    have two : Module.finrank E K=2 := by omega
    rw [two,degree] at tower
    omega
  have size : 3*Module.finrank F E≤Module.finrank F K := by
    rw [←tower,mul_comm 3]
    exact Nat.mul_le_mul_left _ big
  exact subfield_maximum E.val ⟨b,hb⟩ Q nQ sq test hk degree size na

/-- Every ratio in a proper subfield attains the larger dimension for every nonzero scale. -/
theorem absolute_subfield (E : IntermediateField F K) (proper : E ≠ ⊤)
    {b : K} (hb : b ∈ E) {k : ℕ} (hk : 2 ≤ k) (degree : Module.finrank F K = 2*k+1)
    {a : K} (na : a ≠ 0) :
    let L := twoTraces (Algebra.trace F K) a (a*b)
    maxCosetDim F (Space K × (F×F)) (Set.range (lifted L) + Set.range (lifted L)) = k+1 :=
  proper_subfield E proper hb (Algebra.trace F K) (Algebra.trace_ne_zero F K)
    absolute_trace_test.1 absolute_trace_test.2 hk degree na

end Green51OddTrace

#print axioms Green51OddTrace.seventh_orthogonal
#print axioms Green51OddTrace.subfield_maximum
#print axioms Green51OddTrace.proper_subfield
#print axioms Green51OddTrace.absolute_subfield
