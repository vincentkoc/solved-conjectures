import Erdos478CoprimeRootMoments
import Erdos478UnboundedDeficit

/-!
# Products of distinct prime-degree root counts

Two monic irreducibles of coprime degrees have a common root algebra which
is an order in a number field. A minimal polynomial for an integral primitive
element of that field represents the product of their root counts away from
finitely many primes. Its degree is the product of the two input degrees.
-/

namespace Erdos478.RootProduct
noncomputable section
open Polynomial Finset Filter Topology NumberField IntermediateField Module RootPairs RootMoments MeanDeficit

private theorem pair_rank (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hd : 0 < f.natDegree) : finrank ℤ (pairOrder f g) = f.natDegree*g.natDegree := by
  let A := AdjoinRoot f
  let : Nontrivial A := AdjoinRoot.nontrivial f (natDegree_pos_iff_degree_pos.mp hd).ne'
  let h := g.map (AdjoinRoot.of f)
  have hm : h.Monic := hg.map _
  let : Module.Finite ℤ A := hf.finite_adjoinRoot
  let : Module.Free ℤ A := hf.free_adjoinRoot
  let : Module.Finite A (pairOrder f g) := hm.finite_adjoinRoot
  let : Module.Free A (pairOrder f g) := hm.free_adjoinRoot
  rw [← finrank_mul_finrank ℤ A (pairOrder f g),
    (AdjoinRoot.powerBasis' hf).finrank,(AdjoinRoot.powerBasis' hm).finrank]
  exact congrArg (f.natDegree * ·) (hg.natDegree_map _)

private theorem roots_eq_count (K : Type) [Field K] [NumberField K]
    (θ : 𝓞 K) (hθ : ℚ⟮(θ:K)⟯=⊤) {p : ℕ} (hp : p.Prime) (hB : RingOfIntegers.exponent θ < p) :
    roots (minpoly ℤ θ) p = linearCount K p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let h := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hn : h ≠ 0 := ((minpoly.monic θ.isIntegral).map _).ne_zero
  let e : solutions (minpoly ℤ θ) (ZMod p) ≃ h.roots.toFinset :=
    Equiv.subtypeEquivRight fun x => by simp [h,mem_roots hn,IsRoot,eval_map]
  rw [linearCount_eq_roots θ (Nat.not_dvd_of_pos_of_lt (FallingGap.exponent_pos θ hθ) hB)]
  change (Nat.card _ : ℝ) = (h.roots.toFinset.card : ℝ)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

/-- A single irreducible represents the product of the two distinct-root
counts at every sufficiently large prime. -/
theorem fuse (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hi : Irreducible (f.map (algebraMap ℤ ℚ))) (hj : Irreducible (g.map (algebraMap ℤ ℚ)))
    (hc : g.natDegree.Coprime f.natDegree) :
    ∃ h : ℤ[X], h.IsMonicOfDegree (f.natDegree*g.natDegree) ∧
      Irreducible (h.map (algebraMap ℤ ℚ)) ∧
      ∃ B, ∀ p > B, p.Prime → roots h p = roots f p * roots g p := by
  obtain ⟨K,_,_,j,hj',hr⟩ := exists_full_order f g hf hg hi hj hc
  obtain ⟨B,hB⟩ := order_maps_count K j hj' hr
  obtain ⟨θ,hθ⟩ := FallingGap.integral_generator K
  have hdeg : 0 < f.natDegree := by simpa [hf.natDegree_map] using hi.natDegree_pos
  refine ⟨minpoly ℤ θ,⟨(FallingGap.generator_degree θ hθ).trans
    (hr.symm.trans (pair_rank f g hf hg hdeg)),minpoly.monic θ.isIntegral⟩,?_,max B (RingOfIntegers.exponent θ),?_⟩
  · rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := ℚ) (θ : K))
  · intro p hp hpr
    rw [roots_eq_count K θ hθ hpr (lt_of_le_of_lt (le_max_right ..) hp),
      ← hB p (lt_of_le_of_lt (le_max_left ..) hp) hpr]
    rw [← Nat.card_congr (RootPairs.equiv f g (ZMod p)),Nat.card_prod,Nat.cast_mul]
    rfl

/-- Every nonempty family of pairwise coprime degrees admits a single
root polynomial representing its simultaneous root counts. -/
theorem represent {ι : Type*} (f : ι → ℤ[X]) (s : Finset ι) (hs : s.Nonempty)
    (hm : ∀ i ∈ s, (f i).Monic) (hi : ∀ i ∈ s, Irreducible ((f i).map (algebraMap ℤ ℚ)))
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).natDegree.Coprime (f j).natDegree) :
    ∃ h : ℤ[X], h.IsMonicOfDegree (∏ i ∈ s, (f i).natDegree) ∧
      Irreducible (h.map (algebraMap ℤ ℚ)) ∧
      ∃ B, ∀ p > B, p.Prime → roots h p = ∏ i ∈ s, roots (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (not_nonempty_empty hs).elim
  | @insert i s hn ih =>
    have hmi := hm i (mem_insert_self ..)
    have hii := hi i (mem_insert_self ..)
    rcases s.eq_empty_or_nonempty with he|hs
    · subst s
      exact ⟨f i,by simpa using (show (f i).IsMonicOfDegree (f i).natDegree from ⟨rfl,hmi⟩),
        hii,0,fun p _ _ => by simp⟩
    obtain ⟨g,hg,hgi,B,hB⟩ := ih hs (fun j hj => hm j (mem_insert_of_mem hj))
      (fun j hj => hi j (mem_insert_of_mem hj))
      (fun j hj k hk => hc j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
    have hcop : (f i).natDegree.Coprime g.natDegree := by
      rw [hg.natDegree_eq]
      exact Nat.Coprime.prod_right (fun j hj =>
        hc i (mem_insert_self ..) j (mem_insert_of_mem hj) (fun he => hn (he ▸ hj)))
    obtain ⟨h,hd,hir,C,hC⟩ := fuse g (f i) hg.monic hmi hgi hii hcop
    refine ⟨h,by simpa [prod_insert hn,hg.natDegree_eq,mul_comm] using hd,hir,max B C,?_⟩
    intro p hp hpr
    rw [hC p (lt_of_le_of_lt (le_max_right ..) hp) hpr,
      hB p (lt_of_le_of_lt (le_max_left ..) hp) hpr,prod_insert hn,mul_comm]

/-- The limiting mixed root moment is exactly one for each subfamily.
No assumption on the intersections of splitting fields is needed. -/
theorem mixed_mean {ι : Type*} (A : PrimeAverage) (f : ι → ℤ[X]) (s : Finset ι)
    (hm : ∀ i ∈ s, (f i).Monic) (hi : ∀ i ∈ s, Irreducible ((f i).map (algebraMap ℤ ℚ)))
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).natDegree.Coprime (f j).natDegree) :
    Tendsto (fun X => A.avg X (∏ i ∈ s, roots (f i))) atTop (𝓝 1) := by
  rcases s.eq_empty_or_nonempty with he|hs
  · subst s
    simpa using constant_mean A
  obtain ⟨h,hd,hir,B,hB⟩ := represent f s hs hm hi hc
  have changed := A.finite_change (a := ∏ i ∈ s, roots (f i)) (b := roots h) B (by
    intro p hp hpr
    simpa [Finset.prod_apply] using (hB p hp hpr).symm)
  simpa only [sub_add_cancel,zero_add] using changed.add (first_mean A h hd.monic hir)

#print axioms fuse
#print axioms represent
#print axioms mixed_mean

end
end Erdos478.RootProduct
