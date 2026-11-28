import Mathlib

/-! # Independence of consecutive products of distinct linear factors -/
open Polynomial Finset
namespace Green51PencilWindows
variable {K : Type*} [Field K]
noncomputable def window (k : ℕ) (v : ℕ → K) (j : ℕ) : K[X] := ∏ h ∈ range k, (X-C (v (j+h)))

theorem independent (k : ℕ) (v : ℕ → K) (dist : Set.InjOn v (Set.Iio (2*k))) :
    LinearIndependent K (fun i : Fin (k+1) => window k v i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a eq i
  by_contra ni
  let S := univ.filter (fun j : Fin (k+1) => a j≠0)
  have non : S.Nonempty := ⟨i,mem_filter.mpr ⟨mem_univ _,ni⟩⟩
  let m:=S.max' non
  have am : a m≠0 := (mem_filter.mp (S.max'_mem non)).2
  let z:=v (m.val-1)
  by_cases zero : m.val=0
  · have alone : ∑ j : Fin (k+1), a j • window k v j.val = a m • window k v m.val := by
      apply sum_eq_single m
      · intro b _ ne
        have az : a b=0 := by
          by_contra bz
          have le:=S.le_max' b (mem_filter.mpr ⟨mem_univ _,bz⟩)
          exact ne (Fin.ext (by change b.val ≤ m.val at le;omega))
        rw [az,zero_smul]
      · simp
    rw [alone,smul_eq_zero] at eq
    exact ((monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C (v (m.val+j)))).ne_zero) (eq.resolve_left am)
  have vanish (j : Fin (k+1)) (sm : j < m) : (window k v j.val).eval z=0 := by
    simp only [window,eval_prod,eval_sub,eval_X,eval_C]
    apply Finset.prod_eq_zero (i:=m.val-1-j.val) (mem_range.mpr (by have:=m.isLt;omega))
    dsimp [z]
    rw [show j.val+(m.val-1-j.val)=m.val-1 by change j.val < m.val at sm;omega,sub_self]
  have nz : (window k v m.val).eval z≠0 := by
    simp only [window,eval_prod,eval_sub,eval_X,eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj diff
    have eqv := sub_eq_zero.mp diff
    have jm := mem_range.mp hj
    have em : m.val-1=m.val+j := dist (by change m.val-1<2*k;omega) (by change m.val+j<2*k;omega) eqv
    omega
  have h := congrArg (Polynomial.eval z) eq
  simp only [eval_finsetSum,eval_smul,eval_zero] at h
  rw [Finset.sum_eq_single m] at h
  · exact (mul_ne_zero am nz) h
  · intro b _ ne
    by_cases bz : a b=0
    · simp [bz]
    · have le:=S.le_max' b (mem_filter.mpr ⟨mem_univ _,bz⟩)
      simp [vanish b (lt_of_le_of_ne le ne)]
  · simp

/-- A linear relation on coefficients which vanishes on every shifted product is zero. -/
theorem coefficient_test (k : ℕ) (v : ℕ → K) (distinct : Set.InjOn v (Set.Iio (2*k)))
    (a : Fin (k+1) → K)
    (vanish : ∀ j : Fin (k+1), ∑ i : Fin (k+1), a i * (window k v j.val).coeff i.val = 0) :
    ∀ i, a i = 0 := by
  classical
  have small (j : ℕ) : window k v j ∈ degreeLT K (k+1) := by
    apply mem_degreeLT.mpr
    have h : (window k v j).natDegree ≤ k := by
      calc
        _ ≤ ∑ h ∈ range k, (X-C (v (j+h)) : K[X]).natDegree := natDegree_prod_le _ _
        _ = k := by simp
    exact lt_of_le_of_lt (degree_le_natDegree) (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le h))
  let w (j : Fin (k+1)) : degreeLT K (k+1) := ⟨window k v j.val, small j.val⟩
  have independentW : LinearIndependent K w :=
    LinearIndependent.of_comp (degreeLT K (k+1)).subtype (independent k v distinct)
  have spans := independentW.span_eq_top_of_card_eq_finrank' (by
    rw [(degreeLTEquiv K (k+1)).finrank_eq]; simp)
  let φ : K[X] →ₗ[K] K := ∑ i, a i • lcoeff K i.val
  have evalφ (p : K[X]) : φ p = ∑ i, a i * p.coeff i.val := by simp [φ]
  have eq : φ.comp (degreeLT K (k+1)).subtype = 0 :=
    LinearMap.ext_on spans (by rintro _ ⟨j,rfl⟩; exact (evalφ _).trans (vanish j))
  intro i
  have h : (X^i.val : K[X]) ∈ degreeLT K (k+1) := by
    rw [mem_degreeLT, degree_X_pow]; exact WithBot.coe_lt_coe.mpr i.isLt
  have hit := DFunLike.congr_fun eq ⟨X^i.val,h⟩
  change φ (X ^ i.val) = 0 at hit
  simpa [evalφ,coeff_X_pow,Fin.val_inj, mul_ite] using hit

theorem slide (k : ℕ) (v : ℕ → K) (j : ℕ) :
    (X-C (v j))* window k v (j+1) = (X-C (v (j+k)))*window k v j := by
  induction k with
  | zero => simp [window]
  | succ k ih =>
    have step (i : ℕ) : window (k+1) v i = window k v i * (X-C (v (i+k))) := by
      simp [window,Finset.prod_range_succ]
    rw [step,step,←mul_assoc,ih,show j+1+k=j+(k+1) by omega];ring

theorem map_window {F : Type*} [Field F] [Algebra F K]
    (σ : K ≃ₐ[F] K) (b : K) (k j : ℕ) :
    (window k (fun n : ℕ => (σ^n) b) 0).map (σ^j).toRingHom =
      window k (fun n : ℕ => (σ^n) b) j := by
  simp only [window, zero_add, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro h _
  rw [Polynomial.map_sub,map_X,map_C,pow_add]
  rfl

/-- Consecutive Frobenius translates separate every coefficient of the initial window
when the first twice as many conjugates are distinct. -/
theorem coefficients_independent {F : Type*} [Field F] [Algebra F K]
    (σ : K ≃ₐ[F] K) (b : K) (k : ℕ)
    (distinct : Set.InjOn (fun j : ℕ => (σ^j) b) (Set.Iio (2*k))) :
    LinearIndependent F (fun i : Fin (k+1) =>
      (window k (fun j => (σ^j) b) 0).coeff i.val) := by
  classical
  let v (n : ℕ) := (σ^n) b
  have shift (j : ℕ) :
      (window k v 0).map (σ^j).toRingHom = window k v j := by
    simp only [window, zero_add, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro h _
    rw [Polynomial.map_sub,map_X,map_C]
    change X - C ((σ^j) ((σ^h) b)) = X - C ((σ^(j+h)) b)
    rw [pow_add]
    rfl
  rw [Fintype.linearIndependent_iff]
  intro a relation i
  change ∑ h : Fin (k+1), a h • (window k v 0).coeff h.val = 0 at relation
  have vanish (j : Fin (k+1)) :
      ∑ h : Fin (k+1), algebraMap F K (a h) * (window k v j.val).coeff h.val = 0 := by
    have eq := congrArg (σ^j.val) relation
    simp only [map_sum, map_zero, Algebra.smul_def, map_mul, AlgEquiv.commutes] at eq
    rw [← shift j.val]
    simp only [coeff_map]
    exact eq
  exact (FaithfulSMul.algebraMap_injective F K)
    ((coefficient_test k v distinct (fun i => algebraMap F K (a i)) vanish i).trans (map_zero _).symm)

end Green51PencilWindows

#print axioms Green51PencilWindows.independent
#print axioms Green51PencilWindows.coefficient_test
#print axioms Green51PencilWindows.slide
#print axioms Green51PencilWindows.map_window
#print axioms Green51PencilWindows.coefficients_independent
