import CunninghamSparseGapTruncation

/-! Uniqueness from complete coefficient weight and prescribed polynomial endpoints. -/

namespace CunninghamChain.LargeGap
open Polynomial CoefficientEnergy Finset

lemma reflect_energy (P : ℤ[X]) (N : ℕ) :
    energy (reflect N P) (N+1)=energy P (N+1) := by
  rw [←coeff_mul_self_reflect,←coeff_mul_self_reflect,reflect_reflect,mul_comm]

lemma fixed_energy_agreement (F G : ℤ[X]) {N : ℕ} (df : F.natDegree ≤ N) (dg : G.natDegree ≤ N)
    (weight : energy G (N+1)=energy F (N+1))
    (agree : ∀ i ≤ N, F.coeff i≠0 → G.coeff i=F.coeff i) : G=F := by
  have add : energy G (N+1) = energy F (N+1) + energy (G-F) (N+1) := by
    unfold energy
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases h : F.coeff i=0
    · simp [coeff_sub,h]
    · simp [coeff_sub,agree i (by simpa using mem_range.mp hi) h]
  have zero : energy (G-F) (N+1)=0 := by omega
  ext i
  by_cases h : i ≤ N
  · have bound := weight_of_extra (G-F) (m:=0) (Nat.zero_le i) (by omega : i < N+1)
    simp only [energy,sum_range_zero,zero_add,coeff_sub] at bound
    simp only [energy,coeff_sub] at zero
    rw [zero] at bound
    nlinarith only [bound,sq_nonneg (G.coeff i-F.coeff i)]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < i),
      coeff_eq_zero_of_natDegree_lt (by omega : F.natDegree < i)]

/-- The separated polynomial with low term one and the reversed coefficients
of c at the high end, reflected about degree N. -/
noncomputable def separated (c : ℤ[X]) (N : ℕ) := 1+reflect N c

lemma separated_degree (c : ℤ[X]) {N : ℕ} (dc : c.natDegree ≤ N) :
    (separated c N).natDegree ≤ N :=
  natDegree_add_le_of_degree_le (by simp) (natDegree_reflect_le.trans (max_le le_rfl dc))

lemma separated_reflect (c : ℤ[X]) (N : ℕ) : reflect N (separated c N)=X^N+c := by
  simp only [separated,reflect_add,reflect_reflect]
  congr 1
  simpa only [map_one,one_mul] using reflect_C (1:ℤ) N

lemma separated_energy (c : ℤ[X]) {N : ℕ} (dc : c.natDegree < N) :
    energy (separated c N) (N+1)=1+energy c (c.natDegree+1) := by
  have z : (reflect N c).coeff 0=0 := by simp [coeff_eq_zero_of_natDegree_lt dc]
  have add : energy (separated c N) (N+1)=1+energy (reflect N c) (N+1) := by
    have vanish (i : ℕ) : (1:ℤ[X]).coeff (i+1)=0 := by simp [coeff_one]
    simp only [energy,separated,sum_range_succ',coeff_add,coeff_one_zero,vanish,zero_add,
      z,add_zero,one_pow,zero_pow (by decide : 2≠0)]
    ring
  rw [add,reflect_energy,energy_stable c (N:=c.natDegree+1) (by omega) (by omega)]

lemma cut_congr (P Q : ℤ[X]) (m : ℕ) (h : ∀ i < m, P.coeff i=Q.coeff i) :
    cut P m=cut Q m := by
  ext i
  simp only [cut_coeff]
  split_ifs with hi
  · exact h i hi
  · rfl

lemma separated_low (c : ℤ[X]) {N m : ℕ} (hm : c.natDegree < m) (bound : c.natDegree+m ≤ N) :
    cut (separated c N) m=1 ∧ cut (reflect N (separated c N)) m=c := by
  constructor
  · calc _ = cut (1:ℤ[X]) m := cut_congr _ _ _ (fun i hi => by
            simp [separated,coeff_reflect,revAt_le (by omega : i ≤ N),
              coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < N-i)])
         _ = _ := PowerSeries.trunc_coe_eq_self (by simp; omega)
  · rw [separated_reflect]
    have he : cut (X^N+c) m=cut c m := cut_congr _ _ _ fun i hi => by
      simp [coeff_X_pow,show i≠N by omega]
    rw [he]
    exact PowerSeries.trunc_coe_eq_self (by omega)

#print axioms fixed_energy_agreement
#print axioms separated_energy

end CunninghamChain.LargeGap
