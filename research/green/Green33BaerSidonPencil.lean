import Mathlib
/-! Split members of a pencil of ternary quadratic forms over an arbitrary field. -/
open Matrix
namespace Green33BaerSidonPencil
variable {F : Type*} [Field F]

/-- Coefficients in the order X², Y², Z², XY, XZ, YZ. -/
def product (x y : Fin 3→F) : Fin 6→F :=
  ![x 0*y 0,x 1*y 1,x 2*y 2,x 0*y 1+x 1*y 0,
    x 0*y 2+x 2*y 0,x 1*y 2+x 2*y 1]

/-- The integral discriminant works unchanged in characteristic two. -/
def disc (u:Fin 6→F) : F :=
  4*u 0*u 1*u 2+u 3*u 4*u 5-u 0*(u 5)^2-u 1*(u 4)^2-u 2*(u 3)^2

theorem disc_product (x y:Fin 3→F) : disc (product x y)=0 := by
  simp [disc,product]
  ring

/-- A pencil through XY and Z(uX+vY+wZ) can have only one further split
member if the second member shares no factor with the first. -/
theorem additional_split {u v w r:F} (nz:r≠0) (x y:Fin 3→F)
    (split:product x y=![0,0,r*w,1,r*u,r*v]) : r*u*v=w := by
  have h:=disc_product x y
  rw [split] at h
  simp [disc] at h
  exact mul_left_cancel₀ nz (show r*(r*u*v)=r*w by linear_combination h)

theorem unique_additional_split {u v w r s:F} (nonshared : w≠0 ∨ u*v≠0)
    (ln:r≠0) (mn:s≠0) (x y a b:Fin 3→F)
    (first:product x y=![0,0,r*w,1,r*u,r*v]) (second:product a b=![0,0,s*w,1,s*u,s*v]) :
    r=s := by
  have h:=additional_split ln x y first
  have k:=additional_split mn a b second
  have uv:u*v≠0 := by
    rcases nonshared with w0|good
    · intro empty
      rw [mul_assoc,empty,mul_zero] at h
      exact w0 h.symm
    · exact good
  rw [mul_assoc] at h k
  exact mul_right_cancel₀ uv (h.trans k.symm)
#print axioms disc_product
#print axioms unique_additional_split
section Evaluation
variable {K : Type*} [Field K] [Algebra F K]

/-- The six products of a ternary basis in the ambient field. -/
def squares (b:Fin 3→K) : Fin 6→K :=
  ![b 0*b 0,b 1*b 1,b 2*b 2,b 0*b 1,b 0*b 2,b 1*b 2]

theorem evaluate_product (b:Fin 3→K) (x y:Fin 3→F) :
    Fintype.linearCombination F (squares b) (product x y)=
      Fintype.linearCombination F b x*Fintype.linearCombination F b y := by
  simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,squares,product,Algebra.smul_def]
  ring

/-- Independent quadratic products transfer a field equation back to the
ternary pencil, where its discriminant determines the parameter. -/
theorem field_parameter (b:Fin 3→K) (ind:LinearIndependent F (squares b)) {u v w r:F}
    (rn:r≠0) (x y:Fin 3→F)
    (eq:Fintype.linearCombination F b x*Fintype.linearCombination F b y =
      b 0*b 1+r • (b 2*(u • b 0+v • b 1+w • b 2))) :
    r*u*v=w := by
  apply additional_split rn x y
  apply ind.fintypeLinearCombination_injective
  rw [evaluate_product,eq]
  simp [Fintype.linearCombination_apply,Fin.sum_univ_succ,squares,Algebra.smul_def]
  ring
#print axioms field_parameter
end Evaluation

section SquareSpan
open Submodule
open scoped Pointwise
variable {K:Type*} [Field K] [Algebra F K]
/-- The formal rank-six condition is exactly the dimension of the span of
all small-field products, independently of the chosen basis of W. -/
theorem square_span (b:Fin 3→K) :
    (span F (Set.range b))*(span F (Set.range b))=span F (Set.range (squares b)) := by
  rw [span_mul_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_,⟨i,rfl⟩,_,⟨j,rfl⟩,rfl⟩
    fin_cases i <;> fin_cases j <;> first
      | exact ⟨0,rfl⟩
      | exact ⟨1,rfl⟩
      | exact ⟨2,rfl⟩
      | exact ⟨3,rfl⟩
      | exact ⟨4,rfl⟩
      | exact ⟨5,rfl⟩
      | exact ⟨3,mul_comm ..⟩
      | exact ⟨4,mul_comm ..⟩
      | exact ⟨5,mul_comm ..⟩
  · rintro ⟨i,rfl⟩
    apply Set.mem_mul.mpr
    fin_cases i <;> simp [squares,Set.mem_range,Fin.exists_fin_succ]

theorem independent_squares {W:Submodule F K} (rank:Module.finrank F (W*W)=6)
    (b:Fin 3→K) (spans:span F (Set.range b)=W) : LinearIndependent F (squares b) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  change 6=Module.finrank F (span F (Set.range (squares b)))
  rw [←square_span,spans,rank]
#print axioms independent_squares
end SquareSpan

end Green33BaerSidonPencil
