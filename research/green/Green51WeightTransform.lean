import Green51CoordinateStrength
import Mathlib.LinearAlgebra.Matrix.Dual

/-! # The binary MacWilliams identity for finite relation spaces -/

open Finset Green50Downsets Green50Sharp Green51Hadamard
open scoped Classical
namespace Green51WeightTransform
local notation "F" => ZMod 2

/-- Words orthogonal to every relation in the code. -/
noncomputable def dualWords {n : ℕ} (C : Submodule F (Cube n)) : Finset (Cube n) :=
  univ.filter fun z => ∀ c : C, dotProduct z c.val = 0

private theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s h ih => simp [h,sign_add,ih]

private theorem coordinate_product {R : Type*} [CommRing R] {n : ℕ} (z : Cube n) (a b : R) :
    (∏ i, if z i = 0 then a else b) = a ^ (n-(supp z).card) * b ^ (supp z).card := by
  classical
  have comp : (univ.filter fun i => z i=0) = (supp z)ᶜ := by ext; simp [supp]
  rw [prod_ite,comp]
  simp only [prod_const,card_compl,Fintype.card_fin]
  rfl

private theorem binary_transform {R : Type*} [CommRing R] {n : ℕ} (c : Cube n) (t : R) :
    (∑ z : Cube n, t ^ (supp z).card * (sign (dotProduct z c) : R)) =
      (1+t)^(n-(supp c).card)*(1-t)^(supp c).card := by
  classical
  let term (i : Fin n) (b : F) : R := (if b=0 then 1 else t) * (sign (b*c i) : R)
  have term_prod (z : Cube n) : (∏ i, term i (z i))=t^(supp z).card*(sign (dotProduct z c):R) := by
    simp only [term,prod_mul_distrib,coordinate_product,one_pow,one_mul,dotProduct,
      sign_sum,Int.cast_prod]
  have term_sum (i : Fin n) : (∑ b : F, term i b)=if c i=0 then 1+t else 1-t := by
    rw [show (univ : Finset F)={0,1} by decide]
    rcases (show ∀ a:F,a=0 ∨ a=1 by decide) (c i) with h|h <;>
      simp [term,h,sign,sub_eq_add_neg]
  calc
    _ = ∑ z : Cube n, ∏ i,term i (z i) := by simp_rw [term_prod]
    _ = ∏ i, ∑ b:F, term i b := (Fintype.prod_sum term).symm
    _ = _ := by simp_rw [term_sum];exact coordinate_product c _ _

/-- The binary weight enumerator of the orthogonal space over a commutative ring. -/
theorem macwilliams {R : Type*} [CommRing R] {n : ℕ} (C : Submodule F (Cube n)) (t : R) :
    (Fintype.card C : R) * (∑ z ∈ dualWords C, t^(supp z).card) =
      ∑ c : C, (1+t)^(n-(supp c.val).card)*(1-t)^(supp c.val).card := by
  classical
  have ch (z : Cube n) : (∑ c : C, (sign (dotProduct z c.val) : R)) =
      if z∈dualWords C then (Fintype.card C:R) else 0 := by
    let f := (dotProductEquiv F (Fin n) z).comp C.subtype
    have eq : f=0 ↔ z∈dualWords C := by
      simp only [dualWords,mem_filter,mem_univ,true_and,LinearMap.ext_iff]
      rfl
    have h := congrArg (fun a:ℤ => (a:R)) (character_sum f)
    change ((∑ c : C, sign (dotProduct z c.val) : ℤ):R) = _ at h
    rw [Int.cast_sum] at h
    by_cases mem : z∈dualWords C
    · simpa [mem,eq.mpr mem] using h
    · have non : f≠0 := fun hf=>mem (eq.mp hf)
      simpa only [if_neg non,if_neg mem,Int.cast_zero] using h
  calc
    _ = ∑ z : Cube n, t^(supp z).card * (∑ c:C, (sign (dotProduct z c.val):R)) := by
      rw [mul_sum,dualWords,sum_filter]
      simp_rw [ch]
      apply sum_congr rfl
      intro z _
      by_cases mem:z∈dualWords C
      · have h := (mem_filter.mp mem).2
        simp only [if_pos mem,if_pos h,mul_comm]
      · have h : ¬∀c:C,dotProduct z c.val=0 := fun f=>mem (mem_filter.mpr ⟨mem_univ _,f⟩)
        simp only [if_neg mem,if_neg h,mul_zero]
    _ = ∑ z : Cube n, ∑ c:C,t^(supp z).card*(sign (dotProduct z c.val):R) := by simp_rw [mul_sum]
    _ = ∑ c:C, ∑ z : Cube n,t^(supp z).card*(sign (dotProduct z c.val):R) := sum_comm
    _ = _ := by simp_rw [binary_transform]

end Green51WeightTransform
#print axioms Green51WeightTransform.macwilliams
