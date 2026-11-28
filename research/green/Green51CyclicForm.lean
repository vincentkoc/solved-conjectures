import Mathlib
/-! # A cyclic bidiagonal matrix with one vanishing diagonal entry -/
open Fin.NatCast
namespace Green51CyclicForm
variable {K : Type*} [Field K] {k : ℕ} [NeZero k]
def shift (u v : Fin k → K) : (Fin k → K) →ₗ[K] (Fin k → K) where
  toFun x i := u i*x i + v i*x (i+1)
  map_add' x y := by ext i; simp [mul_add]; ring
  map_smul' r x := by ext i; simp; ring
theorem injective {u v : Fin k → K} (first : u 0=0) (all : ∀ i, v i ≠ 0) :
    Function.Injective (shift u v) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have recurrence (i : Fin k) : u i*x i + v i*x (i+1)=0 := congrFun hx i
  have init : x (1 : Fin k)=0 := by
    have eq:=recurrence 0
    simpa [first,all] using eq
  have step (i : Fin k) (h : x i=0) : x (i+1)=0 := by
    simpa [h,all] using recurrence i
  have zeros (n : ℕ) : x ((n:Fin k)+1)=0 := by
    induction n with
    | zero => simpa using init
    | succ n ih => simpa [Nat.cast_succ] using step _ ih
  funext i
  obtain ⟨j,eq⟩ := (Equiv.addRight (1:Fin k)).surjective i
  rw [←eq]
  exact (by simpa using zeros j.val : x (j+1)=0)

noncomputable def cycleForm (u v : Fin k → K) :
    LinearMap.BilinForm K ((Fin k → K) × (Fin k → K)) :=
  LinearMap.mk₂ K (fun x y => ∑ j, (shift u v x.1 j * y.2 j + x.2 j * shift u v y.1 j))
    (by intro x y z; simp [add_mul,Finset.sum_add_distrib]; abel)
    (by intro c x y; simp [mul_assoc,Finset.mul_sum,mul_add])
    (by intro x y z; simp [mul_add,Finset.sum_add_distrib]; abel)
    (by intro c x y; simp [Finset.mul_sum,mul_add]; apply Finset.sum_congr rfl; intro j _; ring)
theorem cycleForm_nondegenerate {u v : Fin k → K} (first : u 0=0) (all : ∀ i,v i≠0) :
    (cycleForm u v).Nondegenerate := by
  have inj := injective first all
  have onto : Function.Surjective (shift u v) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inj
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x h
  have firstPart : shift u v x.1=0 := by
    ext j
    have eq := h (0,Pi.single j 1)
    simpa [cycleForm,Pi.single_apply] using eq
  have zero := (map_eq_zero_iff (shift u v) inj).mp firstPart
  apply Prod.ext zero
  funext j
  obtain ⟨w,hw⟩:=onto (Pi.single j 1)
  have eq:=h (w,0)
  simpa [cycleForm,hw,Pi.single_apply] using eq

end Green51CyclicForm
#print axioms Green51CyclicForm.injective
#print axioms Green51CyclicForm.cycleForm_nondegenerate
