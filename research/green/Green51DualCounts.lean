import Green51WeightTransform

/-! # Dual weight counts for shortened binary codes -/

open Finset Polynomial Green50Downsets Green50Sharp
open scoped Classical
namespace Green51WeightTransform
local notation "F" => ZMod 2

/-- Coefficients of the binary weight transform on an even-weight word. -/
def coefficient (n w j : ℕ) : ℤ :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, ((n-w).choose ij.1 : ℤ) *
    ((-1 : ℤ)^(w-ij.2) * (w.choose ij.2 : ℤ))

private theorem transform_coeff {n w : ℕ} (even : Even w) (j : ℕ) :
    (((1+X : ℤ[X])^(n-w)*(1-X)^w).coeff j) = coefficient n w j := by
  have neg : (1-X : ℤ[X])^w=(X+C (-1))^w := by
    rw [show (1-X : ℤ[X])= -(X+C (-1)) by simp;ring,even.neg_pow]
  rw [neg,coeff_mul]
  simp only [coefficient,coeff_one_add_X_pow,coeff_X_add_C_pow]

/-- Exact counts for any selection of dual weights, including a residue class. -/
theorem dual_count {n : ℕ} (C : Submodule F (Cube n)) (even : ∀ c:C, Even (supp c.val).card)
    (S : Finset ℕ) :
    (Fintype.card C : ℤ)*((dualWords C).filter (fun z=>(supp z).card∈S)).card =
    ∑ c:C,∑ j∈S,coefficient n (supp c.val).card j := by
  classical
  have all := macwilliams C (X:ℤ[X])
  have point (j : ℕ) := congrArg (fun p:ℤ[X]=>p.coeff j) all
  have row (j : ℕ) :
      (Fintype.card C:ℤ)*(∑ z∈dualWords C, if j=(supp z).card then (1:ℤ) else 0) =
      ∑ c:C,coefficient n (supp c.val).card j := by
    simpa only [coeff_natCast_mul,finsetSum_coeff,coeff_X_pow,transform_coeff (even _)] using point j
  calc
    _ = (Fintype.card C:ℤ)*∑ z∈dualWords C,∑ j∈S,if j=(supp z).card then (1:ℤ) else 0 := by
      congr 1
      simp [sum_boole]
    _ = ∑ j∈S,(Fintype.card C:ℤ)*∑ z∈dualWords C,if j=(supp z).card then (1:ℤ) else 0 := by
      rw [sum_comm,mul_sum]
    _ = ∑ j∈S,∑ c:C,coefficient n (supp c.val).card j := sum_congr rfl fun j _=>row j
    _ = _ := sum_comm

/-- The minimum dual weight follows from coordinate surjectivity. -/
theorem no_small_dual {n b : ℕ} (C : Submodule F (Cube n))
    (onto : ∀ T : Finset (Fin n), T.card≤b → ∀ y:T→F,∃ c:C,∀ i:T,c.val i.val=y i)
    {z : Cube n} (hz : z∈dualWords C) (sz : (supp z).card≤b) : z=0 := by
  classical
  by_contra ne
  obtain ⟨i,hi⟩ : ∃ i,z i≠0 := by contrapose! ne;exact funext ne
  have hit : i∈supp z := mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨c,hc⟩ := onto (supp z) sz (fun j => if j.val=i then 1 else 0)
  have point (j:Fin n) : z j*c.val j=if j=i then z i else 0 := by
    by_cases h:j∈supp z
    · rw [hc ⟨j,h⟩]
      by_cases e:j=i <;> simp [e]
    · have v : z j=0 := by simpa [supp] using h
      have e : j≠i := fun e=>h (e ▸ hit)
      simp [v,e]
  have orth := (mem_filter.mp hz).2 c
  simp only [dotProduct,point,sum_ite_eq',mem_univ,if_true] at orth
  exact hi orth

end Green51WeightTransform
#print axioms Green51WeightTransform.dual_count
#print axioms Green51WeightTransform.no_small_dual
