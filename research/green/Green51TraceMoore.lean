import Green51GoldForms
/-! # Frobenius coordinates for the trace pairing -/
open Finset
namespace Green51TraceMoore
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
omit [CharP K 2] in
theorem columns {m : ℕ} (degree : Module.finrank F K=m) {ι : Type*} [Fintype ι]
    (U : Submodule F K) (e : Module.Basis ι F U) :
    LinearIndependent K (fun i : ι => fun j : Fin m => (e i : K)^(2^j.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c relation i
  obtain ⟨l,el⟩ := (e.coord i).exists_extend
  obtain ⟨v,hv⟩ := Green51GoldForms.represent (Algebra.trace F K) (Algebra.trace_ne_zero F K) l
  have dual (t : ι) : Algebra.trace F K (v*(e t : K)) = if t=i then 1 else 0 := by
    rw [←hv]
    have coord := LinearMap.congr_fun el (e t)
    simpa [Module.Basis.coord_apply,Finsupp.single_apply,eq_comm] using coord
  have moments (j : Fin m) : ∑ t, c t * (e t : K)^(2^j.val)=0 := by
    simpa [Finset.sum_apply,Pi.smul_apply] using congrFun relation j
  calc
    c i = ∑ t, c t * algebraMap F K (Algebra.trace F K (v*(e t : K))) := by simp [dual]
    _ = ∑ t, ∑ j : Fin m, c t * v^(2^j.val)*(e t : K)^(2^j.val) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [FiniteField.algebraMap_trace_eq_sum_pow,degree,←Fin.sum_univ_eq_sum_range]
      simp [Nat.card_eq_fintype_card,ZMod.card,mul_pow,Finset.mul_sum,mul_assoc]
    _ = ∑ j : Fin m, v^(2^j.val) * (∑ t, c t*(e t : K)^(2^j.val)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = 0 := by simp [moments]
end Green51TraceMoore
#print axioms Green51TraceMoore.columns
