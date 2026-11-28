import Green51SixTraceSpaces
import Green51TwoGold

/-! # Affine four-spaces for two independent trace tests -/

open Green51GoldSix Green51BCHCompression Green51BCHOptimality Green51GoldForms Polynomial Finset
open scoped Pointwise
namespace Green51SixPencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

theorem normalized_eq (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) {a b : K} (na : a≠0) (nb : b≠0) (ab : a≠b)
    (A : Submodule F K) (dim : Module.finrank F A=4) (inTrace : A≤(artinSchreier (K := K)).range)
    (left : ∀ x∈A, ∀ y∈A,Q (a*bracket x y)=0) (right : ∀ x∈A, ∀ y∈A,Q (b*bracket x y)=0) :
    A=(traceMap (K := K)).ker := by
  let D (u : K) := (bracketForm Q u).ker
  have big : Module.finrank F K+2≤2*Module.finrank F A := by omega
  have first := Green51TwoGold.saturated_radical Q nq sq na A big left
  have second := Green51TwoGold.saturated_radical Q nq sq nb A big right
  have dis : Disjoint (D a) (D b) := Submodule.disjoint_def.mpr (by
    intro x hx hy
    by_contra nx
    apply ab
    apply mul_right_cancel₀ (pow_ne_zero 3 nx)
    rw [(root_criterion Q nq sq na nx).mp hx,(root_criterion Q nq sq nb nx).mp hy])
  have ranks := Submodule.finrank_sup_add_finrank_inf_eq (D a) (D b)
  rw [dis.eq_bot,finrank_bot,add_zero] at ranks
  have eq : D a ⊔ D b=A := Submodule.eq_of_le_of_finrank_le (sup_le first.2 second.2) (by
    rw [ranks]; change _ ≤ Module.finrank F (bracketForm Q a).ker + Module.finrank F (bracketForm Q b).ker
    rw [first.1,second.1,dim])
  have line (u : K) (sub : D u≤A) : D u≤(traceMap (K := K)).ker := by
    intro r hr
    have h := (Green51GoldSix.line_in_trace Q nq sq m r).mp (by
      intro s hs
      apply (test _).mpr
      apply inTrace
      apply sub
      apply (radical Q nq sq u (s*r)).mpr
      rw [mul_pow,hs]
      linear_combination s*((radical Q nq sq u r).mp hr))
    change traceMap r=0
    simpa [trace_apply,relativeTrace,add_comm,add_assoc,add_left_comm] using h
  apply Submodule.eq_of_le_of_finrank_le
  · rw [←eq]; exact sup_le (line a first.2) (line b second.2)
  · rw [trace_dimension m,dim]

open Green51BCH
open scoped Pointwise
def tracePair (Q : K →ₗ[F] F) (a b : K) : K →ₗ[F] F×F :=
  (Q.comp (LinearMap.mulLeft F a)).prod (Q.comp (LinearMap.mulLeft F b))

def HasFour (L : K →ₗ[F] F×F) : Prop :=
  ∃ (p : Space K × (F×F)) (W : Submodule F (Space K × (F×F))), 4≤Module.finrank F W ∧
    p+ᵥ (W : Set _) ⊆ Set.range (lifted L)+Set.range (lifted L)

theorem four_iff_shift (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) {a b : K} (na : a≠0) (nb : b≠0) (ab : a≠b) :
    HasFour (tracePair Q a b) ↔ ∃ t : K,t≠0 ∧ a*t^7∈(coeffMap (K := K)).ker ∧ b*t^7∈(coeffMap (K := K)).ker := by
  let L := tracePair Q a b
  constructor
  · rintro ⟨p,W,dim,sub⟩
    obtain ⟨t,nt,A,ar,inTrace,iso⟩ := Green51BracketRank.trace_space_of_flat L p W sub (by omega)
    have nt7 := pow_ne_zero 7 nt
    have na':=mul_ne_zero na nt7
    have nb':=mul_ne_zero nb nt7
    have fst (x : K) (hx : x∈A) (y : K) (hy : y∈A) : Q ((a*t^7)*bracket x y)=0 := by
      rw [mul_assoc]; exact congrArg Prod.fst (iso x hx y hy)
    have snd (x : K) (hx : x∈A) (y : K) (hy : y∈A) : Q ((b*t^7)*bracket x y)=0 := by
      rw [mul_assoc]; exact congrArg Prod.snd (iso x hx y hy)
    have nl : Q.comp (LinearMap.mulLeft F (a*t^7))≠0 := by
      intro z; apply nq
      ext r
      have eq := LinearMap.congr_fun z ((a*t^7)⁻¹*r)
      change Q ((a*t^7)*((a*t^7)⁻¹*r))=0 at eq
      rwa [←mul_assoc,mul_inv_cancel₀ na',one_mul] at eq
    have lim := isotropic_bound _ nl A fst
    have diff : a*t^7≠b*t^7 := fun h => ab (mul_right_cancel₀ nt7 h)
    have Aeq := normalized_eq m Q nq sq test na' nb' diff A (by omega) inTrace fst snd
    subst A
    exact ⟨t,nt,(coefficient_iff m Q nq sq _).mp fst,(coefficient_iff m Q nq sq _).mp snd⟩
  · rintro ⟨t,nt,ha,hb⟩
    let T := (traceMap (K := K)).ker
    have inside : T≤(artinSchreier (K := K)).range := by
      intro x hx
      apply (test x).mp
      have rel : relativeTrace x=0 := by simpa [relativeTrace,trace_apply,add_comm,add_assoc,add_left_comm] using (show traceMap x=0 from hx)
      simpa using (line_in_trace Q nq sq m x).mpr rel 1 (one_pow 4)
    obtain ⟨p,W,rk,flat⟩ := Green51BracketRank.flat_of_trace_space L t nt T inside (by
      intro x hx y hy
      apply Prod.ext
      · change Q (a*(t^7*bracket x y))=0
        rw [←mul_assoc]; exact (coefficient_iff m Q nq sq _).mpr ha x hx y hy
      · change Q (b*(t^7*bracket x y))=0
        rw [←mul_assoc]; exact (coefficient_iff m Q nq sq _).mpr hb x hx y hy)
    exact ⟨p,W,rk.trans_ge (trace_dimension m).ge,flat⟩

omit [Fintype K] in
theorem coefficient_seven {u : K} (nu : u≠0) (hu : u∈(coeffMap (K := K)).ker) : u^7=1 := by
  have c4 : u^4=u^2+u := CharTwo.add_eq_zero.mp (by simpa [coeff_apply,add_assoc] using (show coeffMap u=0 from hu))
  have c8 : u^8=u := by
    rw [show (8 : ℕ)=4*2 by decide,pow_mul,c4,add_sq,←pow_mul]
    norm_num
    rw [c4]
    ring_nf
    reduce_mod_char!
  apply mul_right_cancel₀ nu
  rw [←pow_succ,c8,one_mul]

theorem canonical_test (m : Module.finrank F K=6) (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (test : ∀ z,Q z=0 ↔ ∃ y : K,y^2+y=z) {a b : K} (na : a≠0) (nb : b≠0) (ab : a≠b) :
    HasFour (tracePair Q a b) ↔ a^36∈(coeffMap (K := K)).ker ∧ b*a^35∈(coeffMap (K := K)).ker := by
  rw [four_iff_shift m Q nq sq test na nb ab]
  constructor
  · rintro ⟨t,nt,ha,hb⟩
    have u7 := coefficient_seven (mul_ne_zero na (pow_ne_zero 7 nt)) ha
    have fix : (a*t^7)^36=a*t^7 := by
      rw [show (36 : ℕ)=7*5+1 by decide,pow_succ,pow_mul,u7,one_pow,one_mul]
    have collapse : (a*t^7)^36=a^36 := by
      rw [mul_pow,←pow_mul,show 7*36=63*4 by decide,pow_mul,pow_sixty_three m nt,one_pow,mul_one]
    have same : a^35=t^7 := by
      apply mul_left_cancel₀ na
      rw [mul_comm a (a^35),←pow_succ,←collapse,fix]
    exact ⟨(collapse.symm.trans fix) ▸ ha, same ▸ hb⟩
  · rintro ⟨ha,hb⟩
    refine ⟨a^5,pow_ne_zero _ na,?_,?_⟩
    · convert ha using 1; ring
    · simpa only [←pow_mul] using hb

end Green51SixPencils

#print axioms Green51SixPencils.normalized_eq
#print axioms Green51SixPencils.four_iff_shift
#print axioms Green51SixPencils.coefficient_seven
#print axioms Green51SixPencils.canonical_test
