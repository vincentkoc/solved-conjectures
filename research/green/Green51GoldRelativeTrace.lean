import Green51BCHScalarProfile
/-! # Relative trace and four-element scalar lines in the field of 64 elements -/
open Green51BCHCompression Green51BCHOptimality Green51GoldForms
open scoped Pointwise
namespace Green51GoldSix
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

omit [CharP K 2] in
/-- Field Frobenius at dimension six. -/
theorem power_sixty_four (m : Module.finrank F K=6) (x : K) : x^64=x := by
  have eq := FiniteField.pow_card x
  rwa [Module.card_eq_pow_finrank (K:=F),ZMod.card,m] at eq

omit [CharP K 2] in
/-- Every nonzero element has order dividing 63. -/
theorem pow_sixty_three (m : Module.finrank F K=6) {x : K} (nx : x≠0) : x^63=1 := by
  apply mul_right_cancel₀ nx
  rw [←pow_succ,power_sixty_four m,one_mul]

/-- The trace from the field of 64 to its four-element subfield. -/
def relativeTrace (r : K) := r+r^4+r^16

omit [Algebra F K] [Fintype K] in
private theorem fourth_add (x y : K) : (x+y)^4=x^4+y^4 := by ring_nf; reduce_mod_char!
private theorem fixed_trace (m : Module.finrank F K=6) (r:K) : (relativeTrace r)^4=relativeTrace r := by
  simp only [relativeTrace,fourth_add,←pow_mul]
  norm_num
  rw [power_sixty_four m];ring

omit [CharP K 2] [Fintype K] in
private theorem trace_fixed (Q : K →ₗ[F] F) (sq : ∀ z,Q (z^2)=Q z) (x:K) :
    Q (relativeTrace x)=Q x := by
  have h4 (v : K) : Q (v^4)=Q v := by rw [show (4:ℕ)=2*2 from rfl,pow_mul,sq,sq]
  rw [relativeTrace,map_add,map_add,show (16:ℕ)=4*4 from rfl,pow_mul,h4,h4,h4,CharTwo.add_self_eq_zero,zero_add]

omit [CharP K 2] [Algebra F K] [Fintype K] in
private theorem trace_mul {a : K} (ha : a^4=a) (r : K) : relativeTrace (a*r)=a*relativeTrace r := by
  have h16 : a^16=a := by rw [show (16:ℕ)=4*4 from rfl,pow_mul,ha,ha]
  simp only [relativeTrace,mul_pow,ha,h16];ring

/-- Multiplication by the four-element subfield stays in the absolute trace hyperplane exactly at relative trace zero. -/
theorem line_in_trace (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (m : Module.finrank F K=6) (r:K) :
    (∀ a:K, a^4=a → Q (a*r)=0) ↔ relativeTrace r=0 := by
  have test (a : K) (ha : a^4=a) : Q (a*r)=Q (a*relativeTrace r) := by
    rw [←trace_mul ha r,trace_fixed Q sq]
  constructor
  · intro h
    by_contra nr
    have non : ∃ u,Q u≠0 := by contrapose! nq;ext x;exact nq x
    obtain ⟨u,nu⟩ := non
    let a := relativeTrace u/relativeTrace r
    have fixed : a^4=a := by simp [a,div_pow,fixed_trace m]
    have vanish := h a fixed
    rw [test a fixed,show a*relativeTrace r=relativeTrace u from div_mul_cancel₀ _ nr,trace_fixed Q sq] at vanish
    exact nu vanish
  · intro z a ha
    rw [test a ha,z,mul_zero,map_zero]

end Green51GoldSix
#print axioms Green51GoldSix.line_in_trace
