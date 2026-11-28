import CunninghamOrbitIsolation

/-! Uniform control of the Selberg collision factor on sparse sets of offsets. -/

namespace CunninghamChain.OrbitIsolation
open Finset Real

private noncomputable def primeWeight (q : ℕ) : ℝ := (q:ℝ)^(-(7/8:ℝ))

private lemma order_weight_tail {ε : ℝ} (he : 0<ε) :
    ∃ R : Finset ℕ, ∀ Q : Finset ℕ, Disjoint Q R → (∀ q∈Q, q.Prime ∧ 2<q) →
      ∑ q∈Q, primeWeight q/orderOf (2:ZMod q) ≤ ε := by
  classical
  let f (q : ℕ) : ℝ := if q.Prime ∧ 2<q then primeWeight q/orderOf (2:ZMod q) else 0
  have sum : Summable f := by
    obtain ⟨C,bnd⟩ := order_weight_bound
    apply summable_of_sum_le (c:=C) (fun q => by dsimp [f,primeWeight]; split <;> positivity)
    intro S
    simpa only [sum_filter,f,primeWeight] using bnd (S.filter fun q => q.Prime ∧ 2<q) (fun _ h => (mem_filter.mp h).2)
  obtain ⟨R,tail⟩ := summable_iff_vanishing_norm.mp sum ε he
  refine ⟨R,fun Q dis hQ => ?_⟩
  have eq : ∑ q∈Q, f q=∑ q∈Q, primeWeight q/orderOf (2:ZMod q) :=
    sum_congr rfl fun q hq => if_pos (hQ q hq)
  have small := tail Q dis
  rw [eq,Real.norm_eq_abs] at small
  exact (le_abs_self _).trans small.le

/-- Offsets j=i+1 carry a uniformly small average collision loss whenever
the set of i has sufficiently small relative cardinality. -/
theorem sparse_collision_loss {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (Q I : Finset ℕ) (H : ℕ), (∀ q∈Q, q.Prime ∧ 2<q) → I⊆range H →
      (∑ i∈I, ∏ q∈Q.filter (fun q => orderOf (2:ZMod q)∣i+1), ((1-1/(q:ℝ))⁻¹)^2)
        ≤ C*I.card+ε*H := by
  classical
  obtain ⟨A,hA,major⟩ := product_loss_bound
  obtain ⟨R,tail⟩ := order_weight_tail (div_pos he hA)
  let M := ∑ q∈R, primeWeight q
  have hn (q : ℕ) : 0≤primeWeight q := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have mp : 0≤M := sum_nonneg fun q _ => hn q
  refine ⟨1+A*M,by positivity,?_⟩
  intro Q I H hQ sub
  let hit (q i : ℕ) := orderOf (2:ZMod q)∣i+1
  let V (i : ℕ) := (Q\R).filter (fun q => hit q i)
  let Z (i : ℕ) := Q.filter fun q => hit q i
  have each (i : ℕ) : ∑ q∈Z i, primeWeight q ≤ M+∑ q∈V i, primeWeight q := by
    have dis : Disjoint R (V i) := disjoint_left.mpr fun q hr hv => (mem_sdiff.mp (mem_filter.mp hv).1).2 hr
    rw [show M=∑ q∈R,primeWeight q from rfl,←sum_union dis]
    apply sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hn q)
    intro q hq
    obtain ⟨mem,test⟩ := mem_filter.mp hq
    by_cases hr : q∈R
    · exact mem_union_left _ hr
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem,hr⟩,test⟩)
  have prop {q : ℕ} (h : q∈Q\R) := hQ q (mem_sdiff.mp h).1
  have full := average_collisions (Q\R) (fun _ h => prop h) H
  have tailBound := tail (Q\R) (disjoint_left.mpr fun _ h hr => (mem_sdiff.mp h).2 hr) (fun _ h => prop h)
  have rest : ∑ i∈I, ∑ q∈V i, primeWeight q ≤ H*(ε/A) :=
    (sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => sum_nonneg fun q _ => hn q)).trans
      (full.trans (mul_le_mul_of_nonneg_left tailBound (Nat.cast_nonneg _)))
  calc _ ≤ ∑ i∈I, (1+A*M+A*(∑ q∈V i, primeWeight q)) := by
            apply sum_le_sum
            intro i _
            apply (major (Z i) (fun q h => (hQ q (mem_filter.mp h).1).1)).trans
            have eq := mul_le_mul_of_nonneg_left (each i) hA.le
            change 1+A*(∑ q∈Z i,primeWeight q) ≤ _
            linarith only [eq]
       _ = (1+A*M)*I.card+A*(∑ i∈I,∑ q∈V i,primeWeight q) := by
            rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_comm (I.card:ℝ)]
       _ ≤ _ := by
            have h := mul_le_mul_of_nonneg_left rest hA.le
            have eq : A*(H*(ε/A))=ε*H := by field_simp
            linarith only [h,eq]

#print axioms sparse_collision_loss

end CunninghamChain.OrbitIsolation
