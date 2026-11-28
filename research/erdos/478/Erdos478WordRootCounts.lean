import Erdos478JointRootBound
import Erdos478GapSplittingTest

/-!
# Counting tuples of polynomial roots at a prime

An integer weight separates all characteristic-zero tuples. Outside finitely
many primes the weighted sum gives a bijection from tuples of rational roots
to the rational roots of its integral word polynomial.
-/

namespace Erdos478.CollisionLaw
open Polynomial Finset EffectiveResolvent RootPairs RootMoments

private theorem root_entries {I K : Type*} [Fintype I] [Field K] (b : I → K) (x : K) :
    (∏ i, (X-C (b i))).IsRoot x ↔ ∃ i, x=b i := by
  simp [IsRoot,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

private theorem lift_solution {R K : Type*} [Field R] [Field K] (j : R →+* K)
    (f : ℤ[X]) (x : R) :
    (f.map (Int.castRingHom K)).IsRoot (j x) ↔ f.eval₂ (Int.castRingHom R) x=0 := by
  have he : (f.map (Int.castRingHom R)).map j=f.map (Int.castRingHom K) := by
    rw [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom K)]
  rw [← he,isRoot_map_iff j.injective]
  simp [IsRoot,eval_map]

/-- At a prime preserving separability, the word polynomial counts all tuples
of rational roots, with an independent choice for each occurrence of an input. -/
theorem word_root_count {n : ℕ} (f : Fin n → ℤ[X]) (d : Fin n → ℕ)
    (hm : ∀ i, (f i).Monic) (hd : ∀ i, (f i).natDegree=d i)
    (M p : ℕ) [Fact p.Prime]
    (hs : ∀ i, ((f i).map (Int.castRingHom (ZMod p))).Separable)
    (hW : ((wordPolynomial n f d (M:ℤ)).map (Int.castRingHom (ZMod p))).Separable) :
    roots (wordPolynomial n f d (M:ℤ)) p = ∏ i, roots (f i) p := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let j := algebraMap (ZMod p) K
  let W := wordPolynomial n f d (M:ℤ)
  have lift (P : ℤ[X]) : (P.map (Int.castRingHom (ZMod p))).map j=P.map (Int.castRingHom K) := by
    rw [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom K)]
  choose a ha using fun i => enumerate_roots ((f i).map (Int.castRingHom K)) ((hm i).map _)
    (IsAlgClosed.splits _) (lift _ ▸ (hs i).map (f:=j)) (((hm i).natDegree_map _).trans (hd i))
  let val (t : Word d) := wordValue (M:K) (fun i => a i (t i))
  have hw : W.map (Int.castRingHom K)=∏ t : Word d, (X-C (val t)) := by
    dsimp only [W]
    rw [wordPolynomial_map]
    simp_rw [ha]
    simpa [val] using wordPolynomial_factors d (fun i => a i) (M:K)
  have hinj : Function.Injective val := by
    have hsep : (W.map (Int.castRingHom K)).Separable := lift _ ▸ hW.map (f:=j)
    rw [hw] at hsep
    exact hsep.injective_of_prod_X_sub_C
  have entry (i : Fin n) (x : K) : ((f i).map (Int.castRingHom K)).IsRoot x ↔ ∃ l, x=a i l := by
    rw [ha,root_entries]
  have target (x : ZMod p) : W.eval₂ (Int.castRingHom (ZMod p)) x=0 ↔ ∃ t, j x=val t := by
    rw [← lift_solution j W,hw,root_entries]
  let T := (i : Fin n) → solutions (f i) (ZMod p)
  have index (x : T) (i) := (entry i _).mp ((lift_solution j _ _).mpr (x i).property)
  choose ind hind using index
  let sum (x : T) := wordValue (M:ZMod p) (fun i => (x i).val)
  have hsum (x : T) : j (sum x)=val (ind x) := by
    simp [sum,val,wordValue,hind]
  let g (x : T) : solutions W (ZMod p) := ⟨sum x,(target _).mpr ⟨ind x,hsum x⟩⟩
  have one : Function.Injective g := by
    intro x y h
    have he : val (ind x)=val (ind y) := (hsum x).symm.trans
      ((congrArg j (congrArg Subtype.val h)).trans (hsum y))
    have hxy := hinj he
    funext i
    exact Subtype.ext (j.injective ((hind x i).trans ((congrArg (a i) (congrFun hxy i)).trans (hind y i).symm)))
  have onto : Function.Surjective g := by
    intro z
    obtain ⟨t,ht⟩ := (target z).mp z.property
    let φ := frobenius K p
    have hz : φ (j z)=j z := by rw [frobenius_def,← map_pow,ZMod.pow_card]
    have closed (i l) : ∃ u, φ (a i l)=a i u := by
      apply (entry i _).mp
      have h := ((entry i _).mpr ⟨l,rfl⟩).map (f:=φ)
      rwa [Polynomial.map_map,RingHom.ext_int (φ.comp _) (Int.castRingHom K)] at h
    have fixed := fixed_word d (fun i => a i) φ M closed hinj t ((congrArg φ ht).symm.trans (hz.trans ht))
    have pre (i) : ∃ x : ZMod p, j x=a i (t i) := by
      have hp : (a i (t i))^p=a i (t i) := fixed i
      obtain ⟨m,he⟩ := (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr hp)
      exact ⟨(m:ZMod p),by simpa [j] using he⟩
    choose u hu using pre
    let x (i) : solutions (f i) (ZMod p) := ⟨u i,(lift_solution j _ _).mp ((entry i _).mpr ⟨t i,hu i⟩)⟩
    refine ⟨x,Subtype.ext (j.injective ?_)⟩
    change j (sum x)=j z
    rw [hsum,ht]
    congr 1
    funext i
    exact (a i).injective ((hind x i).symm.trans (hu i))
  have he := Nat.card_congr (Equiv.ofBijective g ⟨one,onto⟩)
  change (Nat.card (solutions W (ZMod p)) : ℝ)=∏ i, (Nat.card (solutions (f i) (ZMod p)) : ℝ)
  rw [← he]
  change (Nat.card ((i : Fin n) → solutions (f i) (ZMod p)) : ℝ)=_
  simp only [Nat.card_pi,Nat.cast_prod]

#print axioms word_root_count
end Erdos478.CollisionLaw
