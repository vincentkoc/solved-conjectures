import Green51TraceMoore
import Green51CyclicForm
/-! # Pairing Frobenius trace coordinates in even field degree -/
open Finset Green51BCHCompression
open Fin.NatCast
namespace Green51FrobeniusPencil
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
abbrev fr (i : ℕ) : K →+* K := iterateFrobenius K 2 i
omit [Algebra F K] [Fintype K] in
theorem fr_apply (i : ℕ) (x : K) : fr i x=x^(2^i) := rfl
def pair (k : ℕ) (x : K) : (Fin k → K) × (Fin k → K) :=
  (fun j => fr (2*j.val) x, fun j => fr (2*j.val+1) x)
omit [CharP K 2] [Algebra F K] [Fintype K] in
theorem sum_pairs (f : ℕ → K) (k : ℕ) :
    ∑ i ∈ range (2*k), f i = ∑ j ∈ range k, (f (2*j)+f (2*j+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]
    abel
theorem trace_pairs {k : ℕ} (dim : Module.finrank F K=2*k) (z : K) :
    algebraMap F K (Algebra.trace F K z) = ∑ j : Fin k, ((pair k z).1 j+(pair k z).2 j) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,dim]
  rw [sum_pairs,←Fin.sum_univ_eq_sum_range]
  simp only [Nat.card_eq_fintype_card,ZMod.card,pair,fr_apply]
omit [Algebra F K] [Fintype K] in
theorem fr_next (i : ℕ) (x : K) : (fr i x)^2=fr (i+1) x := by
  change (x^(2^i))^2=x^(2^(i+1))
  rw [←pow_mul,pow_succ]
theorem wrap {k : ℕ} [NeZero k] (degree : Module.finrank F K=2*k) (x : K) (j : Fin k) :
    (pair k x).1 (j+1) = fr (2*j.val+2) x := by
  by_cases last : j.val+1=k
  · have zero : j+1=0 := by
      have toNat : j+1 = ((j.val+1:ℕ) : Fin k) := by simp
      rw [toNat,last]; simp
    rw [zero]
    change x^(2^(2*(0:Fin k).val))=x^(2^(2*j.val+2))
    have sz := Module.card_eq_pow_finrank (K:=F) (V:=K)
    rw [ZMod.card,degree,show 2*k=2*j.val+2 by omega] at sz
    rw [←sz,FiniteField.pow_card]
    simp
  · have small : j.val+1<k := by omega
    have val : (j+1).val=j.val+1 := Fin.val_add_one_of_lt' small
    change fr (2*(j+1).val) x = _
    rw [val,show 2*(j.val+1)=2*j.val+2 by omega]
omit [Algebra F K] [Fintype K] in
theorem edge_value (j : ℕ) (a x y : K) :
    fr j (a*bracket x y)=fr j a*(fr (j+1) x*fr j y+fr j x*fr (j+1) y) := by
  rw [←fr_next,←fr_next]
  simp only [bracket,map_mul,map_add]
  ring

theorem trace_cycle {k : ℕ} [NeZero k] (dim : Module.finrank F K=2*k) (a x y : K) :
    algebraMap F K (Algebra.trace F K (a*bracket x y)) =
      Green51CyclicForm.cycleForm (pair k a).1 (pair k a).2 (pair k x) (pair k y) := by
  rw [trace_pairs dim]
  change _=∑ j : Fin k, (Green51CyclicForm.shift (pair k a).1 (pair k a).2 (pair k x).1 j*(pair k y).2 j
    +(pair k x).2 j*Green51CyclicForm.shift (pair k a).1 (pair k a).2 (pair k y).1 j)
  apply Finset.sum_congr rfl
  intro j _
  change fr (2*j.val) (a*bracket x y) + fr (2*j.val+1) (a*bracket x y) =
    (fr (2*j.val) a*fr (2*j.val) x + fr (2*j.val+1) a*(pair k x).1 (j+1))*fr (2*j.val+1) y +
    fr (2*j.val+1) x * (fr (2*j.val) a*fr (2*j.val) y + fr (2*j.val+1) a*(pair k y).1 (j+1))
  rw [edge_value,edge_value,wrap dim,wrap dim]
  ring

omit [Algebra F K] [Fintype K] in
theorem pencil_combine {k : ℕ} [NeZero k] (a b : K) (x y : (Fin k → K) × (Fin k → K)) :
    let w (i : ℕ) := fr i a * (fr i b + b)
    Green51CyclicForm.cycleForm (fun j : Fin k => w (2*j.val)) (fun j => w (2*j.val+1)) x y =
      Green51CyclicForm.cycleForm (pair k (a*b)).1 (pair k (a*b)).2 x y +
      b*Green51CyclicForm.cycleForm (pair k a).1 (pair k a).2 x y := by
  dsimp only
  simp only [Green51CyclicForm.cycleForm,LinearMap.mk₂_apply,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Green51CyclicForm.shift,LinearMap.coe_mk,AddHom.coe_mk,pair,map_mul]
  ring


theorem rel_columns {k : ℕ} (degree : Module.finrank F K = 2*k) {ι : Type*} [Fintype ι]
    (U : Submodule F K) (e : Module.Basis ι F U) :
    LinearIndependent K (fun i : ι => pair k (e i : K)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c relation i
  apply (Fintype.linearIndependent_iff.mp (Green51TraceMoore.columns degree U e)) c _ i
  ext j
  let t : Fin k := ⟨j.val/2,by have hj:=j.isLt;omega⟩
  by_cases par : j.val%2=0
  · have idx : 2*t.val = j.val := by dsimp [t];omega
    simpa [Finset.sum_apply,Prod.fst_sum,Pi.smul_apply,pair,idx,fr_apply] using
      congrFun (congrArg Prod.fst relation) t
  · have idx : 2*t.val+1 = j.val := by dsimp [t];omega
    simpa [Finset.sum_apply,Prod.snd_sum,Pi.smul_apply,pair,idx,fr_apply] using
      congrFun (congrArg Prod.snd relation) t


theorem isotropic_ceiling {k : ℕ} [NeZero k] (degree : Module.finrank F K = 2*k)
    {a : K} (na : a≠0) {b : K} (moves : ∀ i : Fin k, fr (2*i.val+1) b ≠ b)
    (U : Submodule F K) (iso : ∀ x∈U, ∀ y∈U,
      Algebra.trace F K (a*bracket x y)=0 ∧ Algebra.trace F K ((a*b)*bracket x y)=0) :
    Module.finrank F U ≤ k := by
  classical
  let u (i : Fin k) := fr (2*i.val) a*(fr (2*i.val) b+b)
  let v (i : Fin k) := fr (2*i.val+1) a*(fr (2*i.val+1) b+b)
  let B := Green51CyclicForm.cycleForm u v
  have first : u 0=0 := by simp [u,fr_apply,CharTwo.add_self_eq_zero]
  have other (i : Fin k) : v i ≠ 0 :=
    mul_ne_zero (by simpa only [fr_apply] using pow_ne_zero (2^(2*i.val+1)) na)
      (fun zero => moves i (CharTwo.add_eq_zero.mp zero))
  have nonsingular := Green51CyclicForm.cycleForm_nondegenerate first other
  let e := Module.finBasis F U
  let w (i : Fin (Module.finrank F U)) := pair k (e i : K)
  let S := Submodule.span K (Set.range w)
  have rank : Module.finrank K S = Module.finrank F U := by
    simpa [S,w] using finrank_span_eq_card (rel_columns degree U e)
  have kill (i j : Fin (Module.finrank F U)) : B (w i) (w j)=0 := by
    obtain ⟨l,r⟩ := iso _ (e i).property _ (e j).property
    rw [show B (w i) (w j) = _ from pencil_combine a b _ _,←trace_cycle degree,←trace_cycle degree,r,l]
    simp
  have contained : S≤B.orthogonal S := by
    apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    have inKer : S ≤ (B.flip (w i)).ker := by
      apply Submodule.span_le.mpr
      rintro z ⟨j,rfl⟩
      exact kill j i
    exact fun x hx => inKer hx
  have size := Submodule.finrank_mono contained
  rw [LinearMap.BilinForm.finrank_orthogonal nonsingular,rank,Module.finrank_prod] at size
  simp only [Module.finrank_fin_fun] at size
  omega

end Green51FrobeniusPencil

#print axioms Green51FrobeniusPencil.trace_pairs
#print axioms Green51FrobeniusPencil.wrap
#print axioms Green51FrobeniusPencil.edge_value
#print axioms Green51FrobeniusPencil.trace_cycle
#print axioms Green51FrobeniusPencil.pencil_combine
#print axioms Green51FrobeniusPencil.rel_columns
#print axioms Green51FrobeniusPencil.isotropic_ceiling
