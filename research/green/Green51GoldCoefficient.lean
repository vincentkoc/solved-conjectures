import Green51GoldRelativeTrace

/-! # A degree-36 scalar test in the field of 64 elements -/

open Green51BCHCompression Green51BCHOptimality Green51GoldForms
open scoped Pointwise
namespace Green51GoldSix
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [CharP K 2] in
private theorem order_nine_element (m : Module.finrank F K=6) :
    ∃ r : K, r^9=1 ∧ r^3≠1 := by
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Kˣ)
  rw [Nat.card_units,Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=F),ZMod.card,m] at hg
  norm_num at hg
  refine ⟨(g:K)^7,?_,?_⟩
  · have h := pow_orderOf_eq_one g
    rw [hg] at h
    have eq : (g^7)^9=1 := by rw [←pow_mul];exact h
    simpa using congrArg (fun v:Kˣ => (v:K)) eq
  · intro h
    have eq : (g^7)^3=1 := Units.ext (by simpa using h)
    rw [←pow_mul] at eq
    have dv := orderOf_dvd_of_pow_eq_one eq
    rw [hg] at dv
    norm_num at dv

omit [CharP K 2] [Algebra F K] [Fintype K] in
private theorem trace_equation {r : K} (nr : r≠0) :
    relativeTrace r=0 ↔ (r^3)^5+r^3+1=0 := by
  have f : relativeTrace r=r*((r^3)^5+r^3+1) := by unfold relativeTrace;ring
  rw [f,mul_eq_zero];simp [nr]

/-- A degree-nine power of the trace coefficient determines the scalar profile. -/
theorem coefficient_test (m : Module.finrank F K=6) {c : K} (nc : c≠0) :
    (∃ r:K,r≠0 ∧ relativeTrace r=0 ∧ (c*r^3)^9=1) ↔ c^9=1 ∨ (c^9)^3+c^9+1=0 := by
  let v := c^9
  have v7 : v^7=1 := by dsimp only [v];rw [←pow_mul];exact pow_sixty_three m nc
  constructor
  · rintro ⟨r,nr,z,good⟩
    let u := r^3
    have eq : u^5+u+1=0 := (trace_equation nr).mp z
    have fact : (u^2+u+1)*(u^3+u^2+1)=u^5+u+1 := by ring_nf;reduce_mod_char!
    rw [←fact] at eq
    change (c*u)^9=1 at good
    rw [mul_pow] at good
    change v*u^9=1 at good
    rcases mul_eq_zero.mp eq with a|b
    · have id : u^3-1=(u-1)*(u^2+u+1) := by ring
      have u3 : u^3=1 := sub_eq_zero.mp (by rw [id,a,mul_zero])
      left
      change v=1
      have u9 : u^9=1 := by rw [show u^9=(u^3)^3 from by ring,u3,one_pow]
      simpa only [u9,mul_one] using good
    · have id : u^7+1=(u+1)*(u^3+u+1)*(u^3+u^2+1) := by ring_nf;reduce_mod_char!
      have u7 : u^7=1 := CharTwo.add_eq_zero.mp (by rw [id,b,mul_zero])
      have vu : v=u^5 := by
        calc
          v=v*(u^7)^2 := by rw [u7];simp
          _=(v*u^9)*u^5 := by ring
          _=u^5 := by rw [good,one_mul]
      right
      change v^3+v+1=0
      have u15 : (u^5)^3=u := by calc
        _=u*(u^7)^2 := by ring
        _=u := by rw [u7];simp
      rw [vu,u15,add_comm u (u^5)]
      exact (trace_equation nr).mp z
  · intro h
    rcases h with a|b
    · obtain ⟨r,r9,r3⟩ := order_nine_element (K:=K) m
      have nr : r≠0 := by intro e;simp [e] at r9
      let u := r^3
      have u3 : u^3=1 := by dsimp only [u];rw [←pow_mul];exact r9
      have f : (u-1)*(u^2+u+1)=0 := by linear_combination u3
      have q : u^2+u+1=0 := (mul_eq_zero.mp f).resolve_left (sub_ne_zero.mpr r3)
      have u5 : u^5=u^2 := by calc
        _=u^3*u^2 := by ring
        _=u^2 := by rw [u3,one_mul]
      refine ⟨r,nr,(trace_equation nr).mpr ?_,?_⟩
      · change u^5+u+1=0
        rw [u5];exact q
      · rw [mul_pow,a,one_mul,show (9:ℕ)=3*3 from rfl,pow_mul]
        change (u^3)^3=1
        rw [u3,one_pow]
    · change v^3+v+1=0 at b
      refine ⟨v,pow_ne_zero _ nc,(trace_equation (pow_ne_zero _ nc)).mpr ?_,?_⟩
      · change (v^3)^5+v^3+1=0
        rw [show (v^3)^5=v*(v^7)^2 from by ring,v7]
        simpa [add_comm v (v^3)] using b
      · rw [mul_pow]
        change v*(v^3)^9=1
        rw [show v*(v^3)^9=(v^7)^4 from by ring,v7,one_pow]


open Polynomial Finset in
/-- Exactly 36 scalar parameters in the field of 64 pass the coefficient test. -/
theorem count_coefficients (m : Module.finrank F K=6) [DecidableEq K] :
    (univ.filter (fun c:K => c^9=1 ∨ (c^9)^3+c^9+1=0)).card=36 := by
  classical
  let A := univ.filter (fun c:K => c^9=1 ∨ (c^9)^3+c^9+1=0)
  let B := univ.filter (fun c:K => c^27+c^18+1=0)
  let P : Polynomial K := (X^9-1)*(X^27+X^9+1)
  let D : Polynomial K := X^27+X^18+1
  have hp : P.natDegree=36 := by dsimp only [P];compute_degree!
  have hd : D.natDegree=27 := by dsimp only [D];compute_degree!
  have pn : P≠0 := by intro eq;rw [eq,natDegree_zero] at hp;omega
  have dn : D≠0 := by intro eq;rw [eq,natDegree_zero] at hd;omega
  have ca := card_le_degree_of_subset_roots (p:=P) (Z:=A) (by
    intro x hx
    apply (mem_roots pn).mpr
    change P.eval x=0
    simp only [P,eval_mul,eval_sub,eval_add,eval_X,eval_pow,eval_one,mul_eq_zero,sub_eq_zero]
    rcases (mem_filter.mp hx).2 with left|right
    · exact Or.inl left
    · exact Or.inr (by simpa only [←pow_mul] using right))
  have cb := card_le_degree_of_subset_roots (p:=D) (Z:=B) (by
    intro x hx
    apply (mem_roots dn).mpr
    change D.eval x=0
    simpa only [D,eval_add,eval_X,eval_pow,eval_one] using (mem_filter.mp hx).2)
  have cover : univ.erase (0:K)⊆A ∪ B := by
    intro x hx
    have nx := (mem_erase.mp hx).1
    have p := pow_sixty_three m nx
    have fact : (x^9-1)*(x^27+x^9+1)*(x^27+x^18+1)=x^63-1 := by ring_nf;reduce_mod_char!
    have zero : (x^9-1)*(x^27+x^9+1)*(x^27+x^18+1)=0 := by rw [fact,p,sub_self]
    rcases mul_eq_zero.mp zero with a|b
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rcases mul_eq_zero.mp a with s|s
      · exact Or.inl (sub_eq_zero.mp s)
      · exact Or.inr (by simpa only [←pow_mul] using s)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,b⟩)
  have sz := card_le_card cover
  rw [card_erase_of_mem (mem_univ _),card_univ,Module.card_eq_pow_finrank (K:=F),ZMod.card,m] at sz
  have le := card_union_le A B
  rw [hp] at ca
  rw [hd] at cb
  change A.card=36
  omega

end Green51GoldSix
#print axioms Green51GoldSix.coefficient_test
#print axioms Green51GoldSix.count_coefficients
