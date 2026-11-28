import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits

/-! # Reduction of integral roots at a prime of separable reduction -/

namespace Erdos478.LocalWitness
open Polynomial NumberField Function
open scoped Classical
noncomputable section

abbrev Roots {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) := ↥f.roots.toFinset

theorem mem_root_values {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} (h : f.Monic) (x : R) :
    x∈f.roots.toFinset ↔ f.IsRoot x := by simp [mem_roots h.ne_zero]

variable (K : Type*) [Field K]

def integralRootEquiv (f : ℤ[X]) (hm : f.Monic) :
    Roots (f.map (Int.castRingHom (𝓞 K))) ≃ Roots (f.map (Int.castRingHom K)) := by
  let O := 𝓞 K
  let inc := algebraMap O K
  have ev (z : O) : inc ((f.map (Int.castRingHom O)).eval z)=(f.map (Int.castRingHom K)).eval (inc z) := by
    rw [← Polynomial.eval_map_apply,Polynomial.map_map,show inc.comp (Int.castRingHom O)=Int.castRingHom K from Subsingleton.elim _ _]
  let F (z : Roots (f.map (Int.castRingHom O))) : Roots (f.map (Int.castRingHom K)) :=
    ⟨inc z.val,(mem_root_values (hm.map _) _).mpr (by
      rw [IsRoot.def,← ev,show (f.map (Int.castRingHom O)).eval z.val=0 from (mem_root_values (hm.map _) _).mp z.prop,map_zero])⟩
  apply Equiv.ofBijective F
  constructor
  · intro z w he
    have h : (F z).val=(F w).val := congrArg Subtype.val he
    exact Subtype.ext (FaithfulSMul.algebraMap_injective O K h)
  · intro x
    have root := (mem_root_values (hm.map _) _).mp x.prop
    have integ : IsIntegral ℤ x.val := ⟨f,hm,by
      rw [← eval_map,show algebraMap ℤ K=Int.castRingHom K from Subsingleton.elim _ _]
      exact root⟩
    let z : O := ⟨x.val,integ⟩
    have rz := (FaithfulSMul.algebraMap_injective O K) (show inc ((f.map (Int.castRingHom O)).eval z)=inc 0 by
      rw [map_zero,ev]; exact root)
    exact ⟨⟨z,(mem_root_values (hm.map _) _).mpr rz⟩,rfl⟩

theorem integral_root_count (f : ℤ[X]) (hm : f.Monic) (sep : (f.map (Int.castRingHom K)).Separable)
    (sp : (f.map (Int.castRingHom K)).Splits) :
    (f.map (Int.castRingHom (𝓞 K))).roots.card=(f.map (Int.castRingHom (𝓞 K))).natDegree := by
  classical
  have eq := Fintype.card_congr (integralRootEquiv K f hm)
  simp only [Roots,Fintype.card_coe,Multiset.toFinset_card_of_nodup (nodup_roots sep)] at eq
  have le := Multiset.toFinset_card_le (f.map (Int.castRingHom (𝓞 K))).roots
  have cap := card_roots' (f.map (Int.castRingHom (𝓞 K)))
  rw [← sp.natDegree_eq_card_roots,hm.natDegree_map] at eq
  rw [hm.natDegree_map] at cap ⊢
  omega

/-- When the image polynomial is separable and all roots already lie in the
source domain, reduction bijects its distinct roots onto the residue roots. -/
def reduceRoots {A B : Type*} [CommRing A] [IsDomain A] [Field B] (h : A →+* B)
    (f : A[X]) (hm : f.Monic) (full : f.roots.card=f.natDegree) (sep : (f.map h).Separable) :
    Roots f ≃ Roots (f.map h) := by
  classical
  have eq := hm.roots_map_of_card_eq_natDegree h full
  have nd : (f.roots.map h).Nodup := eq ▸ nodup_roots sep
  have inj := (Multiset.nodup_map_iff_inj_on (Multiset.Nodup.of_map _ nd)).mp nd
  let F (z : Roots f) : Roots (f.map h) :=
    ⟨h z.val,Multiset.mem_toFinset.mpr (eq ▸ Multiset.mem_map.mpr ⟨z.val,Multiset.mem_toFinset.mp z.prop,rfl⟩)⟩
  apply Equiv.ofBijective F
  constructor
  · intro x y he
    exact Subtype.ext (inj _ (Multiset.mem_toFinset.mp x.prop) _ (Multiset.mem_toFinset.mp y.prop) (congrArg Subtype.val he))
  · intro y
    have hy := Multiset.mem_toFinset.mp y.prop
    have img : y.val∈f.roots.map h := eq.symm ▸ hy
    obtain ⟨x,hx,he⟩ := Multiset.mem_map.mp img
    exact ⟨⟨x,Multiset.mem_toFinset.mpr hx⟩,Subtype.ext he⟩

theorem reduceRoots_val {A B : Type*} [CommRing A] [IsDomain A] [Field B] (h : A →+* B)
    (f : A[X]) (hm : f.Monic) (full : f.roots.card=f.natDegree) (sep : (f.map h).Separable) (x : Roots f) :
    (reduceRoots h f hm full sep x).val=h x.val := rfl

theorem integralRootEquiv_val (f : ℤ[X]) (hm : f.Monic) (x : Roots (f.map (Int.castRingHom (𝓞 K)))) :
    (integralRootEquiv K f hm x).val=(x.val : K) := rfl

#print axioms Roots
#print axioms mem_root_values
#print axioms integralRootEquiv
#print axioms integral_root_count
#print axioms reduceRoots
#print axioms reduceRoots_val
#print axioms integralRootEquiv_val
end
end Erdos478.LocalWitness
