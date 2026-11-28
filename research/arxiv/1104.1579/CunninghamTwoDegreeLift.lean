import Mathlib

/-! Lifting a reflected product from two configurations of exponents. -/

namespace CunninghamChain.GapLift
open Polynomial Finset

variable {ι : Type*} [Fintype ι]

noncomputable def assemble (x : ι → ℕ) (a : ι → ℚ) : ℚ[X] :=
  ∑ i, monomial (x i) (a i)

/-- The outer variable records exponent displacement between two configurations. -/
noncomputable def liftTerms (M : ℕ) (x y : ι → ℕ) (a : ι → ℚ) : (ℚ[X])[X] :=
  ∑ i, monomial (M+x i-y i) (monomial (x i) (a i))

lemma eval_one_lift (M : ℕ) (x y : ι → ℕ) (a : ι → ℚ) :
    (liftTerms M x y a).eval 1 = assemble x a := by
  simp [liftTerms,assemble,eval_finsetSum,eval_monomial]

/-- An additive map can record an arbitrary second exponent separately at each degree. -/
private noncomputable def tag (f : ℕ → ℕ) : ℚ[X] →+ (ℚ[X])[X] where
  toFun P := P.sum (fun d c => monomial (f d) (monomial d c))
  map_zero' := by simp
  map_add' P Q := sum_add_index P Q _ (by simp) (by simp)

private lemma tag_monomial (f : ℕ → ℕ) (n : ℕ) (c : ℚ) :
    tag f (monomial n c)=monomial (f n) (monomial n c) := by
  simp [tag]

private lemma tag_product (M : ℕ) (x y u v : ι → ℕ) (a b : ι → ℚ) (f : ℕ → ℕ)
    (comp : ∀ i j, f (x i+u j)=(M+x i-y i)+(M+u j-v j)) :
    tag f (assemble x a * assemble u b) = liftTerms M x y a * liftTerms M u v b := by
  simp only [assemble,liftTerms,sum_mul,mul_sum,map_sum,monomial_mul_monomial,tag_monomial,comp]

/-- If equal exponent differences stay equal in the second configuration, any
identity of reflected products lifts, with the original rational coefficients. -/
theorem lift_product_eq {N M : ℕ} (x y : ι → ℕ)
    (hx : ∀ i, x i ≤ N) (hy : ∀ i, y i ≤ M)
    (same : ∀ i j k l, x i+(N-x j)=x k+(N-x l) → y i+(M-y j)=y k+(M-y l))
    (a b : ι → ℚ)
    (prod : assemble x a*assemble (fun i => N-x i) a =
      assemble x b*assemble (fun i => N-x i) b) :
    liftTerms M x y a*liftTerms M (fun i => N-x i) (fun i => M-y i) a =
      liftTerms M x y b*liftTerms M (fun i => N-x i) (fun i => M-y i) b := by
  let f (ij : ι × ι) := x ij.1+(N-x ij.2)
  let g (ij : ι × ι) := (M+x ij.1-y ij.1)+(M+(N-x ij.2)-(M-y ij.2))
  have compatible : g.FactorsThrough f := by
    rintro ⟨i,j⟩ ⟨k,l⟩ eq
    have e := same i j k l eq
    change x i+(N-x j)=x k+(N-x l) at eq
    change (M+x i-y i)+(M+(N-x j)-(M-y j))=(M+x k-y k)+(M+(N-x l)-(M-y l))
    have := hx j; have := hx l; have := hy i; have := hy j; have := hy k; have := hy l
    omega
  obtain ⟨t,et⟩ := (Function.factorsThrough_iff g).mp compatible
  have comp (i j : ι) : t (x i+(N-x j))=(M+x i-y i)+(M+(N-x j)-(M-y j)) :=
    (congrFun et (i,j)).symm
  exact (tag_product M _ _ _ _ a a t comp).symm.trans
    ((congrArg (tag t) prod).trans (tag_product M _ _ _ _ b b t comp))

#print axioms eval_one_lift
#print axioms lift_product_eq

end CunninghamChain.GapLift
