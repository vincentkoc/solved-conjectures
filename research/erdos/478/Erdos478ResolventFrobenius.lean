import Erdos478PermutationResolvent
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Detecting complete splitting from a simple permutation resolvent

A rational root of a separable permutation resolvent forces the Frobenius
endomorphism to fix each root of the input polynomial.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial
open scoped Polynomial

private theorem root_product_iff {ι K : Type*} [Fintype ι] [Field K] (a : ι → K) (z : K) :
    (∏ i, (X-C (a i))).IsRoot z ↔ ∃ i, z = a i := by
  classical
  simp [IsRoot.def,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

private theorem integer_root_map {K : Type*} [Field K] (f : ℤ[X]) (φ : K →+* K) {x : K}
    (hx : (f.map (Int.castRingHom K)).IsRoot x) : (f.map (Int.castRingHom K)).IsRoot (φ x) := by
  have he : φ.comp (Int.castRingHom K) = Int.castRingHom K := RingHom.ext_int ..
  simpa only [Polynomial.map_map,he] using hx.map (f := φ)

private theorem fixed_from_root {K : Type*} [Field K] (φ : K →+* K) {n : ℕ} (a : Fin n ↪ K)
    (f : ℤ[X]) (h : f.map (Int.castRingHom K) = ∏ i, (X-C (a i))) (M : ℕ)
    (hs : ((resolvent n M f).map (Int.castRingHom K)).Separable) (z : K)
    (hz : ((resolvent n M f).map (Int.castRingHom K)).IsRoot z) (hφ : φ z = z) :
    ∀ i, φ (a i) = a i := by
  classical
  rw [resolvent_factors a f h M] at hs hz
  obtain ⟨τ,hτ⟩ := (root_product_iff _ _).mp hz
  apply fixed_of_tag φ a M hs.injective_of_prod_X_sub_C _ τ (hτ ▸ hφ)
  intro i
  have ha : (f.map (Int.castRingHom K)).IsRoot (a i) := by
    rw [h,root_product_iff]
    exact ⟨i,rfl⟩
  have hh := integer_root_map f φ ha
  rwa [h,root_product_iff] at hh

private theorem fixed_in_prime_field (p : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    [Algebra (ZMod p) K] [CharP K p] {x : K} (hx : x^p=x) : x ∈ (algebraMap (ZMod p) K).range := by
  obtain ⟨m,hm⟩ := (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr hx)
  exact ⟨(m : ZMod p),by simpa using hm⟩

/-- Enumerate the roots of a split, monic, separable polynomial by its degree. -/
theorem enumerate_roots {K : Type*} [Field K] (F : K[X]) (hm : F.Monic) (hs : F.Splits)
    (hd : F.Separable) {n : ℕ} (hn : F.natDegree = n) :
    ∃ a : Fin n ↪ K, F = ∏ i, (X-C (a i)) := by
  classical
  let U := F.roots.toFinset
  have hc : U.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hd),← hs.natDegree_eq_card_roots,hn]
  let e : Fin n ≃ ↥U := (Fintype.equivFinOfCardEq (by simpa using hc)).symm
  let a : Fin n ↪ K := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hu : univ.map a = U := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i,_,rfl⟩ := mem_map.mp hx
      exact (e i).property
    · intro hx
      refine mem_map.mpr ⟨e.symm ⟨x,hx⟩,mem_univ _,?_⟩
      change (e (e.symm ⟨x,hx⟩)).val = x
      simp
  have hr : F.roots = univ.val.map a := calc
    F.roots = U.val := (Multiset.dedup_eq_self.mpr (nodup_roots hd)).symm
    _ = (univ.map a).val := congrArg Finset.val hu.symm
    _ = _ := rfl
  refine ⟨a,?_⟩
  rw [hs.eq_prod_roots_of_monic hm,hr]
  simp [Finset.prod,Function.comp_def]

/-- A prime at which the monic input and its permutation resolvent are
separable and the resolvent has a rational root splits the input completely. -/
theorem split_of_resolvent_root (f : ℤ[X]) (hm : f.Monic) (M p : ℕ) [Fact p.Prime]
    (hf : (f.map (Int.castRingHom (ZMod p))).Separable)
    (hR : ((resolvent f.natDegree M f).map (Int.castRingHom (ZMod p))).Separable)
    (hr : ∃ z : ZMod p, ((resolvent f.natDegree M f).map (Int.castRingHom (ZMod p))).IsRoot z) :
    (f.map (Int.castRingHom (ZMod p))).Splits := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let j := algebraMap (ZMod p) K
  have he (g : ℤ[X]) : (g.map (Int.castRingHom (ZMod p))).map j = g.map (Int.castRingHom K) := by
    rw [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom K)]
  let F := f.map (Int.castRingHom K)
  have hsplit : F.Splits := IsAlgClosed.splits _
  have hsep : F.Separable := by simpa only [he] using hf.map (f := j)
  obtain ⟨a,ha⟩ := enumerate_roots F (hm.map _) hsplit hsep (hm.natDegree_map _)
  obtain ⟨z,hz⟩ := hr
  have h₁ := fixed_from_root (frobenius K p) a f ha M
    (he _ ▸ hR.map (f := j)) (j z) (he _ ▸ hz.map (f := j)) (by
      rw [frobenius_def,← map_pow,ZMod.pow_card])
  apply Splits.of_splits_map j (he f ▸ hsplit)
  intro x hx
  rw [he f] at hx
  have hx' : F.IsRoot x := isRoot_of_mem_roots hx
  rw [ha,root_product_iff] at hx'
  obtain ⟨i,rfl⟩ := hx'
  exact fixed_in_prime_field p (h₁ i)

#print axioms enumerate_roots
#print axioms split_of_resolvent_root

end Erdos478.EffectiveResolvent
