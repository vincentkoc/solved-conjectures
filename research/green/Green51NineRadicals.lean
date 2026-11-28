import Green51NineTraceWord
import Green51GoldSix

/-! # Vectors forced by the two bracket forms in field degree nine -/

open Green51BCHCompression Green51GoldForms
namespace Green51NinePencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [Algebra F K] [Fintype K] in
private theorem step1 (g:K) (rel:g^9=g+1) :
    (v1 g)^4 + v1 g = (beta g)^2*((1:K))^4 + beta g*(1:K) := by
  dsimp [v1,beta]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) (g^3+g^5+g^6+g^7+g^10+g^11+g^15+g^19) * rel
omit [Algebra F K] [Fintype K] in
private theorem step2 (g:K) (rel:g^9=g+1) :
    (v2 g)^4 + v2 g = (beta g)^2*(v1 g)^4 + beta g*v1 g := by
  dsimp [v2,v1,beta]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) (g^2+g^4+g^5+g^8+g^11+g^12+g^13+g^14+g^15+g^17+g^18+g^19+g^21+g^23+g^24+g^25+g^27+g^33) * rel
omit [Algebra F K] [Fintype K] in
private theorem step3 (g:K) (rel:g^9=g+1) :
    (v3 g)^4 + v3 g = (beta g)^2*(v2 g)^4 + beta g*v2 g := by
  dsimp [v3,v2,beta]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) (g+g^2+g^3+g^4+g^5+g^7+g^9+g^11+g^16+g^17+g^20+g^21+g^25+g^29) * rel
omit [Algebra F K] [Fintype K] in
private theorem step4 (g:K) (rel:g^9=g+1) :
    (v4 g)^4 + v4 g = (beta g)^2*(v3 g)^4 + beta g*v3 g := by
  dsimp [v4,v3,beta]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) (g+g^2+g^5+g^7+g^8+g^15+g^17+g^22+g^23+g^24+g^25+g^28+g^29+g^31+g^33+g^37) * rel
/-- Every common five-dimensional isotropic space contains all five trace-certificate vectors. -/
theorem chain_forced (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (m : Module.finrank F K=9) (size : Fintype.card K=512) (g : K) (rel : g^9=g+1)
    (U : Submodule F K) (d : 5≤Module.finrank F U)
    (iso : ∀ x∈U,∀ y∈U,Q (bracket x y)=0)
    (iso' : ∀ x∈U,∀ y∈U,Q (beta g * bracket x y)=0) :
    (1:K)∈U ∧ v1 g∈U ∧ v2 g∈U ∧ v3 g∈U ∧ v4 g∈U := by
  let B:=bracketForm Q 1
  have rad : B.ker ≤ Submodule.span F {(1:K)} := by
    intro x hx
    by_cases nx : x=0
    · rw [nx];exact Submodule.zero_mem _
    have cu : x^3=1 := by simpa using (Green51GoldSix.root_criterion Q nq sq one_ne_zero nx).mp hx
    have all := FiniteField.pow_card_sub_one_eq_one x nx
    rw [size,show 512-1=3*170+1 by decide,pow_succ,pow_mul,cu,one_pow,one_mul] at all
    rw [all];exact Submodule.subset_span (Set.mem_singleton _)
  have rk:=Submodule.finrank_mono ((show U⊓B.ker ≤ B.ker from inf_le_right).trans rad)
  rw [finrank_span_singleton one_ne_zero] at rk
  have bound:=B.finrank_add_finrank_orthogonal' U
  have incl : U≤B.orthogonal U := by
    intro u hu x hx
    change Q (1*bracket x u)=0
    simpa using iso x hx u hu
  have equals : U=B.orthogonal U := Submodule.eq_of_le_of_finrank_le incl (by omega)
  have sym (x y : K) : bracket x y=bracket y x := by unfold bracket; ring
  have transfer {x y : K} (prev : x∈U) (rel : y^4+y=(beta g)^2*x^4+beta g*x) : y∈U := by
    rw [equals]
    intro u hu
    change Q (1*bracket u y)=0
    rw [one_mul,sym u y]
    have coef (a z : K) : Q (a*bracket z u) = Q ((a^2*z^4+a*z)*u^2) :=
      bracketForm_apply_squared Q sq a z u
    have eq:=coef 1 y
    simp only [one_pow,one_mul] at eq
    rw [eq,rel,←coef]
    exact iso' x prev u hu
  have z : (1:K)∈U := by
    rw [equals]
    intro u _
    change Q (1*bracket u 1)=0
    rw [one_mul,show bracket u 1=u^2+u by unfold bracket;ring,map_add,sq,CharTwo.add_self_eq_zero]
  have h1:=transfer z (step1 g rel)
  have h2:=transfer h1 (step2 g rel)
  have h3:=transfer h2 (step3 g rel)
  exact ⟨z,h1,h2,h3,transfer h3 (step4 g rel)⟩

end Green51NinePencils
#print axioms Green51NinePencils.chain_forced
