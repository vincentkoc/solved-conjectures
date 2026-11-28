import Green51GoldForms
/-! # Cubic residue classes of projected BCH coefficients -/
open Green51GoldForms Green51BCH Green51BCHCompression
open scoped Pointwise
namespace Green51TwoGold
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

theorem saturated_radical
    (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {c:K} (nc : c≠0) (A : Submodule F K)
    (bound : Module.finrank F K+2≤2*Module.finrank F A)
    (iso : ∀ x∈A,∀ y∈A,Q (c*Green51BCHCompression.bracket x y)=0) :
    Module.finrank F (bracketForm Q c).ker=2 ∧ (bracketForm Q c).ker≤A := by
  let B := bracketForm Q c
  have le : A≤B.orthogonal A := fun y hy x hx => iso x hx y hy
  have h := Submodule.finrank_mono le
  have eq := B.finrank_add_finrank_orthogonal' A
  have ir := Submodule.finrank_mono (show A ⊓ B.ker ≤ B.ker from inf_le_right)
  have rb : Module.finrank F B.ker≤2 := radical_bound Q nq sq nc
  have sat : A ⊓ B.ker=B.ker := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
  change Module.finrank F B.ker=2 ∧ B.ker≤A
  exact ⟨by omega,sat ▸ (show A ⊓ B.ker≤A from inf_le_left)⟩


private theorem cube_of_saturation (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    {c:K} (nc : c≠0) (A : Submodule F K)
    (bound : Module.finrank F K+2≤2*Module.finrank F A)
    (iso : ∀ x∈A,∀ y∈A,Q (c*bracket x y)=0) : ∃ r:K, r≠0 ∧ c*r^3=1 := by
  have rank := (saturated_radical Q nq sq nc A bound iso).1
  obtain ⟨r,mem,nr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show (bracketForm Q c).ker≠⊥ by intro h;rw [h,finrank_bot] at rank;omega)
  refine ⟨r,nr,?_⟩
  have eq := (radical Q nq sq _ _).mp mem
  rw [show c^2*r^4+c*r=(c*r)*(c*r^3+1) by ring] at eq
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left (mul_ne_zero nc nr))


/-- All active coefficients of a pencil supporting an oversized flat belong to a single cubic residue class. -/
theorem cubic_ratios {H:Type*} [AddCommGroup H] [Module F H]
    (Q : K →ₗ[F] F) (nq : Q≠0) (sq : ∀ z,Q (z^2)=Q z)
    (L : K →ₗ[F] H) {a b:K} (na : a≠0) (nb : b≠0)
    (g h : H →ₗ[F] F) (ga : ∀ z,g (L z)=Q (a*z)) (hb : ∀ z,h (L z)=Q (b*z))
    (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p+ᵥ (W:Set _) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (high : 3≤Module.finrank F W) (sat : Module.finrank F K+2≤2*Module.finrank F W) :
    ∃ z:K, z^3=b/a := by
  obtain ⟨t,nt,A,ar,_,iso⟩ := Green51BracketRank.trace_space_of_flat L p W inside high
  have sz : Module.finrank F K+2≤2*Module.finrank F A := by omega
  have forced (c:K) (nc:c≠0) (f:H →ₗ[F] F) (rep : ∀ z,f (L z)=Q (c*z)) :
      ∃ r:K, r≠0 ∧ (c*t^7)*r^3=1 := by
    apply cube_of_saturation Q nq sq (mul_ne_zero nc (pow_ne_zero 7 nt)) A sz
    intro x hx y hy
    rw [mul_assoc,←rep,iso x hx y hy,map_zero]
  obtain ⟨r,_,hr⟩ := forced a na g ga
  obtain ⟨s,ns,hs⟩ := forced b nb h hb
  refine ⟨r/s,?_⟩
  rw [div_pow,div_eq_div_iff (pow_ne_zero 3 ns) na]
  apply mul_left_cancel₀ (pow_ne_zero 7 nt)
  linear_combination hr-hs

end Green51TwoGold
#print axioms Green51TwoGold.saturated_radical
#print axioms Green51TwoGold.cubic_ratios
