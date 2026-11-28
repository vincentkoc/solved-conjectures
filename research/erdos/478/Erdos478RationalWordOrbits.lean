import Erdos478RootOrbitFactorCount
import Erdos478MixedPolynomialMoments

/-!
# Rational irreducible factors of a root-word polynomial

A separating word identifies tuples of roots with roots of one polynomial.
Its irreducible factors correspond to the Galois orbits of those tuples.
-/

namespace Erdos478.CollisionLaw
open Polynomial Finset EffectiveResolvent Function Filter Topology RootMoments
noncomputable section

private theorem equiv_of_root_product {F K I : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype I] {f : F[X]} (hm : f.Monic) (v : I → K) (inj : Injective v)
    (fac : f.map (algebraMap F K) = ∏ i, (X-C (v i))) :
    ∃ e : I ≃ f.rootSet K, ∀ i, (e i : K)=v i := by
  classical
  have root (x : K) : x∈f.rootSet K ↔ ∃ i, x=v i := by
    rw [hm.mem_rootSet,← eval_map_algebraMap,fac]
    simp [eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]
  let g (i : I) : f.rootSet K := ⟨v i,(root _).2 ⟨i,rfl⟩⟩
  have bij : Bijective g := by
    refine ⟨fun _ _ h => inj (congrArg Subtype.val h),?_⟩
    rintro ⟨x,hx⟩
    obtain ⟨i,rfl⟩ := (root _).1 hx
    exact ⟨i,rfl⟩
  exact ⟨Equiv.ofBijective g bij,fun _ => rfl⟩

abbrev RationalWord (fs : List ℤ[X]) (K : Type*) [Field K] [Algebra ℚ K] :=
  (i : Fin fs.length) → ((fs.get i).map (Int.castRingHom ℚ)).rootSet K

/-- Over any common splitting field the separating word is an equivariant encoding.
The displayed evaluation formula makes the encoding usable for automorphisms. -/
theorem rational_word_equiv (fs : List ℤ[X]) (K : Type*) [Field K] [Algebra ℚ K]
    (good : ∀ f∈fs, Good f) (split : ∀ f∈fs,(f.map (Int.castRingHom K)).Splits) :
    ((wordAt fs (weight fs)).map (Int.castRingHom K)).Splits ∧
    ∃ e : RationalWord fs K ≃ ((wordAt fs (weight fs)).map (Int.castRingHom ℚ)).rootSet K,
      ∀ u, (e u : K)=wordValue (weight fs : K) (fun i => (u i : K)) := by
  classical
  let d (i : Fin fs.length) := (fs.get i).natDegree
  let M := weight fs
  let W := wordAt fs M
  have hW : Good W := good_at_weight _ good
  have H (i : Fin fs.length) := good _ (List.get_mem fs i)
  have lift (f : ℤ[X]) : (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ K) = f.map (Int.castRingHom K) := by
    rw [Polynomial.map_map,RingHom.ext_int ((algebraMap ℚ K).comp _) (Int.castRingHom K)]
  choose a ha using fun i => enumerate_roots ((fs.get i).map (Int.castRingHom K))
    ((H i).1.map _) (split _ (List.get_mem fs i)) (lift _ ▸ (H i).2.2.map (f:=algebraMap ℚ K))
    ((H i).1.natDegree_map _)
  let val (t : Word d) := wordValue (M:K) (fun i => a i (t i))
  have fac : W.map (Int.castRingHom K) = ∏ t : Word d, (X-C (val t)) := by
    unfold W wordAt
    rw [wordPolynomial_map]
    simp_rw [ha]
    simpa only [val,Int.coe_castRingHom,Int.cast_natCast] using
      wordPolynomial_factors d (fun i j => a i j) (M:K)
  have sep : (∏ t : Word d, (X-C (val t))).Separable :=
    fac ▸ lift W ▸ hW.2.2.map (f:=algebraMap ℚ K)
  obtain ⟨e,he⟩ := equiv_of_root_product (hW.1.map (Int.castRingHom ℚ)) val
    sep.injective_of_prod_X_sub_C ((lift W).trans fac)
  choose row hrow using fun i => equiv_of_root_product ((H i).1.map (Int.castRingHom ℚ))
    (a i) (a i).injective ((lift _).trans (ha i))
  let r : Word d ≃ RationalWord fs K := Equiv.piCongrRight row
  have sp : (W.map (Int.castRingHom K)).Splits := fac ▸ Splits.prod fun _ _ => Splits.X_sub_C _
  refine ⟨sp,r.symm.trans e,fun u => ?_⟩
  change (e (r.symm u) : K)=_
  rw [he]
  apply congrArg (wordValue (M:K))
  funext i
  exact (hrow i ((r.symm u) i)).symm.trans
    (congrArg Subtype.val (congrFun (r.apply_symm_apply u) i))

/-- The mixed prime root moment equals the number of labels when two
tuples have the same label exactly if they are rationally conjugate. -/
theorem moment_by_labels (fs : List ℤ[X]) (K : Type*) [Field K] [Algebra ℚ K] [Normal ℚ K]
    (good : ∀ f∈fs, Good f) (split : ∀ f∈fs,(f.map (Int.castRingHom K)).Splits)
    {L : Type*} [Fintype L] (tag : RationalWord fs K → L) (onto : Surjective tag)
    (orbit : ∀ u v, tag u=tag v ↔ ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (u i : K)=(v i : K)) :
    moment fs = Fintype.card L := by
  classical
  let W := wordAt fs (weight fs)
  let Q := W.map (Int.castRingHom ℚ)
  have hW := good_at_weight _ good
  obtain ⟨sp,e,he⟩ := rational_word_equiv fs K good split
  have splitQ : (Q.map (algebraMap ℚ K)).Splits := by
    simpa only [Q, W, Polynomial.map_map, RingHom.ext_int
      ((algebraMap ℚ K).comp (Int.castRingHom ℚ)) (Int.castRingHom K)] using sp
  let act (σ : K ≃ₐ[ℚ] K) (u : RationalWord fs K) : RationalWord fs K :=
    fun i => ⟨σ (u i),rootSet_mapsTo σ.toAlgHom (u i).prop⟩
  have natural (σ : K ≃ₐ[ℚ] K) (u : RationalWord fs K) : (e (act σ u) : K)=σ (e u : K) := by
    rw [he,he]
    simp [act,wordValue]
  have same (u v : RationalWord fs K) : tag u=tag v ↔ minpoly ℚ (e u : K)=minpoly ℚ (e v : K) := by
    rw [orbit]
    constructor
    · rintro ⟨σ,hσ⟩
      have eq : act σ u=v := funext fun i => Subtype.ext (hσ i)
      have h := natural σ u
      rw [eq] at h
      rw [h,minpoly.algEquiv_eq]
    · intro h
      obtain ⟨σ,hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp h.symm
      have eq : act σ u=v := e.injective (Subtype.ext ((natural σ u).trans hσ))
      exact ⟨σ,fun i => congrArg Subtype.val (congrFun eq i)⟩
  apply factor_count_by_labels (hW.1.map _) hW.2.2 splitQ (fun x => tag (e.symm x))
    (onto.comp e.symm.surjective)
  intro x y
  simpa only [Equiv.apply_symm_apply] using same (e.symm x) (e.symm y)

/-- A finite product of root counts has prime mean equal to the number
of conjugacy classes of tuples, with arbitrary finite coordinate indices. -/
theorem product_mean_by_labels (A : PrimeAverage) {I L : Type*} [Fintype I] [Fintype L]
    (f : I → ℤ[X]) (K : Type*) [Field K] [Algebra ℚ K] [Normal ℚ K]
    (good : ∀ i, Good (f i)) (split : ∀ i, ((f i).map (Int.castRingHom K)).Splits)
    (tag : ((i : I) → ((f i).map (Int.castRingHom ℚ)).rootSet K) → L) (onto : Surjective tag)
    (orbit : ∀ u v, tag u=tag v ↔ ∃ σ : K ≃ₐ[ℚ] K, ∀ i, σ (u i : K)=(v i : K)) :
    Tendsto (fun X => A.avg X (fun p => ∏ i, roots (f i) p)) atTop (𝓝 (Fintype.card L : ℝ)) := by
  classical
  let e := (Fintype.equivFin I).symm
  let fs := List.ofFn (fun j => f (e j))
  let index : Fin fs.length ≃ I := (finCongr List.length_ofFn).trans e
  have get (i : Fin fs.length) : fs.get i = f (index i) := List.get_ofFn _ _
  let R (i : I) := ((f i).map (Int.castRingHom ℚ)).rootSet K
  let unpack (u : RationalWord fs K) (i : I) : R i :=
    ⟨u (index.symm i),by simpa only [get,Equiv.apply_symm_apply] using (u (index.symm i)).prop⟩
  have surj : Surjective unpack := by
    intro v
    let u : RationalWord fs K := fun i => ⟨v (index i),by rw [get]; exact (v _).prop⟩
    refine ⟨u,funext fun i => Subtype.ext ?_⟩
    change (v (index (index.symm i)) : K)=(v i : K)
    rw [Equiv.apply_symm_apply]
  have gf : ∀ q∈fs, Good q := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact good _
  have sf : ∀ q∈fs, (q.map (Int.castRingHom K)).Splits := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact split _
  have hc := moment_by_labels fs K gf sf (tag ∘ unpack) (onto.comp surj) (by
    intro u v
    change tag (unpack u)=tag (unpack v) ↔ _
    rw [orbit]
    apply exists_congr
    intro σ
    constructor
    · intro h i
      have z := h (index i)
      change σ (u (index.symm (index i)) : K)=(v (index.symm (index i)) : K) at z
      exact (congrArg (fun j => σ (u j : K)=(v j : K)) (index.symm_apply_apply i)).mp z
    · exact fun h i => h (index.symm i))
  have lim := mixed_root_mean A fs gf
  rw [hc] at lim
  have eq : productRoots fs = fun p => ∏ i, roots (f i) p := by
    funext p
    unfold productRoots fs
    rw [List.map_ofFn,List.prod_ofFn]
    exact e.prod_comp (fun i => roots (f i) p)
  simpa only [eq] using lim

#print axioms product_mean_by_labels
#print axioms moment_by_labels
#print axioms RationalWord
#print axioms rational_word_equiv
end
end Erdos478.CollisionLaw
