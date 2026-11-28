import CunninghamCoefficientEnergy

/-! An explicit multiplier whose second difference has a large isolated leading coefficient. -/

namespace CunninghamChain.CoefficientEnergy
open Polynomial

private noncomputable def fromList : List ℤ → ℤ[X]
  | [] => 0
  | a::t => C a + X*fromList t

private lemma fromList_coeff (l : List ℤ) (i : ℕ) :
    (fromList l).coeff i = l[i]?.getD 0 := by
  induction l generalizing i with
  | nil => simp [fromList]
  | cons a t ih =>
    cases i with
    | zero => simp [fromList]
    | succ j => rw [fromList,coeff_add,coeff_C,coeff_X_mul,ih]; simp

/-- Coefficients in ascending order of the sum of
X^(64−2i)(1+X+⋯+X^(i−1))² for 1 ≤ i ≤ 32. -/
private def entries : List ℤ :=
  [1,2,4,6,9,12,16,20,25,30,36,42,49,56,64,72,
   81,90,100,110,121,132,144,156,169,182,196,210,225,240,256,272,
   287,300,312,322,331,338,344,348,351,352,352,350,347,342,336,328,
   319,308,296,282,267,250,232,212,191,168,144,118,91,62,32]

noncomputable def multiplier : ℤ[X] := fromList entries

private def entry (i : ℕ) : ℤ := entries[i]?.getD 0

private lemma coeff_entry (i : ℕ) : multiplier.coeff i = entry i := fromList_coeff ..

set_option maxRecDepth 4096 in
lemma multiplier_shape : multiplier.natDegree=62 ∧ multiplier.leadingCoeff=32 := by
  have top : multiplier.coeff 62=32 := by rw [coeff_entry]; decide
  have hd : multiplier.natDegree≤62 := natDegree_le_iff_coeff_eq_zero.mpr (by
    intro i hi
    have bound : entries.length ≤ i := by change 63 ≤ i; omega
    simp [coeff_entry,entry,List.getElem?_eq_none bound])
  have eq : multiplier.natDegree=62 :=
    le_antisymm hd (le_natDegree_of_ne_zero (p:=multiplier) (by rw [top]; decide))
  exact ⟨eq,show multiplier.coeff multiplier.natDegree=32 from eq.symm ▸ top⟩

private def secondDiff (i : ℕ) : ℤ :=
  (if 2 ≤ i then entry (i-2) else 0) - 2*(if 1 ≤ i then entry (i-1) else 0) + entry i

private lemma curvature_coeff (i : ℕ) :
    ((X-1)^2*multiplier).coeff i = secondDiff i := by
  have h : (X-1)^2*multiplier =
      X^2*multiplier-C (2:ℤ)*(X^1*multiplier)+multiplier := by
    rw [show C (2:ℤ)=(2:ℤ[X]) by norm_num]; ring
  rw [h,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow_mul',coeff_X_pow_mul',secondDiff]
  simp only [coeff_entry]

private def partialSum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => partialSum f n + f n

private lemma sum_as_partial (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = partialSum f n := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => rw [Finset.sum_range_succ,ih,partialSum]

/-- The large coefficient 32 has been omitted from the second sum. The two
finite certificates are independent of the seed coefficient, index and sign. -/
theorem multiplier_energy : energy multiplier 64 = 3023024 ∧
    energy ((X-1)^2*multiplier) 64=96 := by
  simp only [energy,coeff_entry,curvature_coeff,sum_as_partial]
  decide

#print axioms multiplier_shape
#print axioms multiplier_energy

end CunninghamChain.CoefficientEnergy
