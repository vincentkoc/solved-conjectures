import Green51MooreRank
import Green51SeventhPowerFibre

/-! # Prescribed binary Moore determinants through one direction -/

open Green50Downsets Green51BCH
open scoped Pointwise
namespace Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]

def bracket (x y : K) : K := x*y*(x+y)

omit [Algebra F K] in
theorem moore_bracket (t b c : K) :
    moore t b c=t * bracket (b*(b+t)) (c*(c+t)) := by
  rw [moore_prod]
  unfold bracket
  ring_nf
  reduce_mod_char!

omit [Algebra F K] in
theorem double_bracket (x y z : K) :
    bracket (bracket x y) (bracket x z)=x^2*moore x y z := by
  rw [moore_prod]
  unfold bracket
  ring_nf
  reduce_mod_char!


/-- Three squares of independent field elements occur as the three pair minors. -/
theorem realize_minors_of_meeting [Fintype K] (u v w : K) (non : moore u v w ≠ 0)
    (meets : Green51BCHOptimality.MeetsSeventhPowers K) :
    ∃ t a b c : K, t≠0 ∧ moore t b c=u^2 ∧ moore t a c=v^2 ∧ moore t a b=w^2 := by
  let D := moore u v w
  let g : Fin 3 → K := ![bracket v w,bracket u w,bracket u v]
  obtain ⟨s,ns,ok⟩ := Green51BCHOptimality.simultaneous_of_meeting (fun i => D^2*g i) meets
  choose z hz using ok
  let t := (s^3*D)⁻¹
  have nt : t≠0 := inv_ne_zero (mul_ne_zero (pow_ne_zero _ ns) non)
  let a := fun i => t*z i
  have take (i) : a i*(a i+t)=s*g i := by
    calc a i*(a i+t)=t^2*((z i)^2+z i) := by dsimp [a];ring
         _ = _ := by rw [hz];dsimp [t];field_simp [ns,show D≠0 from non]
  have pair (i j : Fin 3) : moore t (a i) (a j)=bracket (g i) (g j)/D := by
    rw [moore_bracket,take,take]
    dsimp [t];unfold bracket;field_simp [ns,show D≠0 from non]
  have law (r s h : K) : moore r s h=moore r h s ∧ moore r s h=moore s r h ∧ moore r s h=moore h r s := by
    rw [moore_prod,moore_prod s r h,moore_prod h r s,moore_prod r h s]
    exact ⟨by ring,by ring,by ring⟩
  have sym (r s : K) : bracket r s=bracket s r := by unfold bracket;ring
  refine ⟨t,a 0,a 1,a 2,nt,?_,?_,?_⟩
  · rw [pair]
    change bracket (bracket u w) (bracket u v) /D=u^2
    rw [double_bracket,←(law u v w).1,mul_div_cancel_right₀ _ non]
  · rw [pair]
    change bracket (bracket v w) (bracket u v) /D=v^2
    rw [sym u v,double_bracket,←(law v u w).1,←(law u v w).2.1,mul_div_cancel_right₀ _ non]
  · rw [pair]
    change bracket (bracket v w) (bracket u w) /D=w^2
    rw [sym v w,sym u w,double_bracket,←(law w u v).1,←(law u v w).2.2,mul_div_cancel_right₀ _ non]

/-- Three squares of independent field elements occur as the three pair minors. -/
theorem realize_minors [Fintype K] (u v w : K) (non : moore u v w ≠ 0)
    (large : 10 ≤ Module.finrank F K ∨ 4 ≤ Module.finrank F K ∧ (Nat.card Kˣ).Coprime 7) :
    ∃ t a b c : K, t≠0 ∧ moore t b c=u^2 ∧ moore t a c=v^2 ∧ moore t a b=w^2 :=
  realize_minors_of_meeting u v w non (Green51BCHOptimality.meets_of_large large)

end Green51BCHCompression

#print axioms Green51BCHCompression.moore_bracket
#print axioms Green51BCHCompression.double_bracket
#print axioms Green51BCHCompression.realize_minors_of_meeting
#print axioms Green51BCHCompression.realize_minors
