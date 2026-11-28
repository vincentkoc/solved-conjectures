import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

/-! # Separating a doubly transitive root action into two rational factors -/

namespace Erdos478.PrimeDifferences
open Polynomial
open scoped Polynomial
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

private theorem monic_antisymm {f g : F[X]} (hf : f.Monic) (hg : g.Monic)
    (h : f∣g) (hh : g∣f) : f=g :=
  (eq_of_monic_of_dvd_of_natDegree_le hf hg h (natDegree_le_of_dvd hh hf.ne_zero)).symm

/-- For a separable polynomial splitting in K, two classes of conjugate roots
give exactly two irreducible factors. -/
theorem two_minpolys {f : F[X]} (hm : f.Monic) (hs : f.Separable)
    (hsp : (f.map (algebraMap F K)).Splits) (u v : K)
    (hu : aeval u f=0) (hv : aeval v f=0) (hne : minpoly F u≠minpoly F v)
    (hcover : ∀ x : K, aeval x f=0 → minpoly F x=minpoly F u ∨ minpoly F x=minpoly F v) :
    f=minpoly F u*minpoly F v := by
  have iu : IsIntegral F u := .of_finite F u
  have iv : IsIntegral F v := .of_finite F v
  have cop : IsCoprime (minpoly F u) (minpoly F v) := by
    apply ((minpoly.irreducible iu).isCoprime_or_dvd _).resolve_right
    intro h
    exact hne (monic_antisymm (minpoly.monic iu) (minpoly.monic iv) h
      ((minpoly.irreducible iu).dvd_symm (minpoly.irreducible iv) h))
  have hm' := (minpoly.monic iu).mul (minpoly.monic iv)
  apply monic_antisymm hm hm' _ (cop.mul_dvd (minpoly.dvd F u hu) (minpoly.dvd F v hv))
  apply (map_dvd_map' (algebraMap F K)).mp
  apply hsp.dvd_of_roots_le_roots (hm.map _).ne_zero
  apply (Multiset.le_iff_subset (nodup_roots (hs.map (f:=algebraMap F K)))).mpr
  intro x hx
  apply (mem_roots (hm'.map _).ne_zero).mpr
  rw [IsRoot.def,eval_map_algebraMap,map_mul,mul_eq_zero]
  obtain h | h := hcover x (by simpa only [← eval_map_algebraMap,← IsRoot.def] using isRoot_of_mem_roots hx)
  · exact Or.inl (h ▸ minpoly.aeval F x)
  · exact Or.inr (h ▸ minpoly.aeval F x)

variable [Normal F K] {I : Type*}

/-- The separated diagonal pairs form one conjugacy class and the separated
off-diagonal pairs form the other. -/
theorem pair_factors (v : I → K) (M : ℕ) (i j : I) (hij : i≠j)
    (closed : ∀ (σ : K ≃ₐ[F] K) (x : I), ∃ y, σ (v x)=v y)
    (conj : ∀ x y z w : I, x≠y → z≠w → ∃ σ : K ≃ₐ[F] K, σ (v x)=v z ∧ σ (v y)=v w)
    (inj : Function.Injective (fun q : I × I => v q.1+(M:K)*v q.2))
    {f : F[X]} (hm : f.Monic) (hs : f.Separable)
    (hsp : (f.map (algebraMap F K)).Splits)
    (hr : ∀ x : K, aeval x f=0 ↔ ∃ a b, x=v a+(M:K)*v b) :
    f=minpoly F (v i+(M:K)*v i)*minpoly F (v i+(M:K)*v j) := by
  classical
  let t (a b : I) := v a+(M:K)*v b
  have cov (a b : I) : minpoly F (t a b)=minpoly F (t i i) ∨ minpoly F (t a b)=minpoly F (t i j) := by
    have other (a : I) : ∃ c, a≠c := if ha : a=i then ⟨j,ha ▸ hij⟩ else ⟨i,ha⟩
    by_cases h : a=b
    · subst b
      obtain ⟨c,hac⟩ := other a
      obtain ⟨σ,hσ,_⟩ := conj i j a c hij hac
      left
      simpa [t,hσ] using minpoly.algEquiv_eq σ (t i i)
    · obtain ⟨σ,hσ,hτ⟩ := conj i j a b hij h
      right
      simpa [t,hσ,hτ] using minpoly.algEquiv_eq σ (t i j)
  apply two_minpolys hm hs hsp (t i i) (t i j)
    ((hr _).mpr ⟨i,i,rfl⟩) ((hr _).mpr ⟨i,j,rfl⟩)
  · intro eq
    obtain ⟨σ,hσ⟩ := isConjRoot_iff_exists_algEquiv.mp (isConjRoot_def.mpr eq.symm)
    obtain ⟨u,hu⟩ := closed σ i
    have he : (u,u)=(i,j) := inj (by simpa [t,hu] using hσ)
    exact hij ((congrArg Prod.fst he).symm.trans (congrArg Prod.snd he))
  · intro x hx
    obtain ⟨a,b,rfl⟩ := (hr _).mp hx
    exact cov a b

#print axioms two_minpolys
#print axioms pair_factors
end
end Erdos478.PrimeDifferences
