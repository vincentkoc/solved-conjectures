import Mathlib

/-! # Common parameter subspaces for rank constraints -/
namespace Green52CubicMinors
local notation "𝔽" => ZMod 2
variable {U X Y : Type*} [AddCommGroup U] [Module 𝔽 U] [Finite U]
  [AddCommGroup X] [Module 𝔽 X] [Finite X] [AddCommGroup Y] [Module 𝔽 Y]

/-- A rank-r minor of a linear matrix family stays nonsingular on a translate
of a parameter subspace of codimension at most r squared. -/
theorem freeze_minor (T : U →ₗ[𝔽] X →ₗ[𝔽] Y) (a : U) (r : ℕ)
    (hr : r ≤ Module.finrank 𝔽 (T a).range) :
    ∃ H : Submodule 𝔽 U, Module.finrank 𝔽 U ≤ Module.finrank 𝔽 H + r^2 ∧
      ∀ h : H, r ≤ Module.finrank 𝔽 (T (a+h.val)).range := by
  classical
  let E := Fin r → 𝔽
  have de : Module.finrank 𝔽 E = r := by simp [E]
  obtain ⟨i,inj⟩ := finrank_le_iff_exists_linearMap.mp (show Module.finrank 𝔽 E ≤ Module.finrank 𝔽 (T a).range by rw [de]; exact hr)
  let I := (T a).range.subtype.comp i
  have ii : Function.Injective I := (T a).range.subtype_injective.comp inj
  obtain ⟨p,hp⟩ := I.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr ii)
  obtain ⟨j,hj⟩ := (T a).rangeRestrict.exists_rightInverse_of_surjective (T a).range_rangeRestrict
  let J := j.comp i
  have id_at (x : E) : p (T a (J x)) = x := by
    have e : T a (j (i x)) = (i x).val := congrArg Subtype.val (LinearMap.congr_fun hj (i x))
    exact (congrArg p e).trans (LinearMap.congr_fun hp x)
  let Q : U →ₗ[𝔽] E →ₗ[𝔽] E :=
    { toFun := fun u => p.comp ((T u).comp J)
      map_add' := by intro b c; ext x; simp
      map_smul' := by intro c b; ext x; simp }
  refine ⟨Q.ker,?_,?_⟩
  · have total := Q.finrank_range_add_finrank_ker
    have le := Submodule.finrank_le Q.range
    rw [Module.finrank_linearMap,de,←sq] at le
    omega
  · intro h
    have eq (x : E) : p (T (a+h.val) (J x))=x := by
      have hz : p (T h.val (J x))=0 := LinearMap.congr_fun (show Q h.val=0 from h.property) x
      rw [map_add,LinearMap.add_apply,map_add,id_at,hz,add_zero]
    let Z := (T (a+h.val)).rangeRestrict.comp J
    have iz : Function.Injective Z := by
      intro x y hxy
      exact (eq x).symm.trans ((congrArg (fun z => p z.val) hxy).trans (eq y))
    calc
      r = Module.finrank 𝔽 E := de.symm
      _ ≤ _ := LinearMap.finrank_le_finrank_of_injective (f:=Z) iz
end Green52CubicMinors
#print axioms Green52CubicMinors.freeze_minor

open Finset
open scoped Pointwise
namespace Green52CubicSelection
local notation "𝔽" => ZMod 2
variable {U ι : Type*} [Fintype ι] [AddCommGroup U] [Module 𝔽 U] [Fintype U]

/-- A subspace of codimension at most N contains a direction outside a union
of N sets, each having density at most 2⁻²ᴺ. -/
theorem avoid_sparse (N : ℕ) (hi : Fintype.card ι ≤ N) (H : Submodule 𝔽 U)
    (hd : Module.finrank 𝔽 U ≤ Module.finrank 𝔽 H + N) (bad : ι → Finset U)
    (small : ∀ i, 2^(2*N)*(bad i).card ≤ Fintype.card U) :
    ∃ a ∈ H, ∀ i, a ∉ bad i := by
  classical
  let covered := univ.biUnion bad
  let A := (H:Set U).toFinset
  have ca : A.card=Fintype.card H := by simp [A,Set.toFinset_card]
  have size : Fintype.card U ≤ 2^N*A.card := by
    rw [ca,Module.card_eq_pow_finrank (K:=𝔽) (V:=U),Module.card_eq_pow_finrank (K:=𝔽) (V:=H)]
    simp only [ZMod.card,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sum := Finset.sum_le_sum (s:=(univ:Finset ι)) (fun i _ => small i)
  rw [←mul_sum] at sum
  simp only [sum_const,card_univ,nsmul_eq_mul] at sum
  have cover : 2^(2*N)*covered.card ≤ N*(2^N*A.card) :=
    ((Nat.mul_le_mul_left _ card_biUnion_le).trans sum).trans (Nat.mul_le_mul hi size)
  have pow : N*2^N < 2^(2*N) := by
    rw [two_mul,pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self) (by positivity)
  have pos : 0<A.card := ca ▸ Fintype.card_pos
  have less : covered.card < A.card := by
    apply Nat.lt_of_mul_lt_mul_left (a:=2^(2*N))
    exact cover.trans_lt (by simpa [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right pow pos)
  obtain ⟨a,ha,out⟩ := exists_mem_notMem_of_card_lt_card less
  refine ⟨a,by simpa [A] using ha,fun i h => out ?_⟩
  exact mem_biUnion.mpr ⟨i,mem_univ _,h⟩

/-- Intersect finitely many parameter subspaces while adding the dimension costs. -/
theorem common_subspace (F : ι → Submodule 𝔽 U) (b : ι → ℕ)
    (bound : ∀ i, Module.finrank 𝔽 U ≤ Module.finrank 𝔽 (F i) + b i) :
    ∃ J : Submodule 𝔽 U, (∀ i, J ≤ F i) ∧
      Module.finrank 𝔽 U ≤ Module.finrank 𝔽 J + ∑ i, b i := by
  classical
  let Q := LinearMap.pi (fun i => (F i).mkQ)
  refine ⟨Q.ker,?_,?_⟩
  · intro i x hx
    exact (Submodule.Quotient.mk_eq_zero (F i)).mp (congrFun (show Q x=0 from hx) i)
  · have dim := Q.finrank_range_add_finrank_ker
    have le := Submodule.finrank_le Q.range
    rw [Module.finrank_pi_fintype] at le
    have bnd (i) : Module.finrank 𝔽 (U ⧸ F i) ≤ b i := by
      have eq := (F i).finrank_quotient_add_finrank
      have h := bound i
      omega
    exact dim ▸ (by have := le.trans (sum_le_sum (fun i _ => bnd i)); omega)
end Green52CubicSelection
#print axioms Green52CubicSelection.avoid_sparse
#print axioms Green52CubicSelection.common_subspace
