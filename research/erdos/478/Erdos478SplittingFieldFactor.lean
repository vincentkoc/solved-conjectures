import Erdos478SplittingFactorCount
import Erdos478DisjointGapFamilies

/-!
# A separating root ordering generates the splitting field

A Galois automorphism fixing a separated tag fixes the entire ordered list
of roots. Its minimal polynomial therefore has degree equal to the
splitting-field degree and divides the integral permutation resolvent.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset Filter Topology IntermediateField EffectiveResolvent RootMoments
open scoped Classical

noncomputable abbrev SplitField (f : ℤ[X]) := (f.map (Int.castRingHom ℚ)).SplittingField

private theorem map_rat {K : Type*} [Field K] [Algebra ℚ K] (f : ℤ[X]) :
    (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ K)=f.map (Int.castRingHom K) := by
  rw [Polynomial.map_map,RingHom.ext_int ((algebraMap ℚ K).comp _) (Int.castRingHom K)]

private theorem root_prod {I K : Type*} [Fintype I] [Field K] (a : I → K) (x : K) :
    (∏ i, (X-C (a i))).IsRoot x ↔ ∃ i, x=a i := by
  simp [IsRoot,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

private theorem tag_generates {f : ℤ[X]} (hsep : (f.map (Int.castRingHom ℚ)).Separable)
    (a : Fin f.natDegree ↪ SplitField f)
    (hf : f.map (Int.castRingHom (SplitField f))=∏ i, (X-C (a i)))
    (M : ℕ) (hs : Function.Injective fun σ => tag a σ (M:SplitField f)) :
    ℚ⟮tag a (Equiv.refl _) (M:SplitField f)⟯=⊤ := by
  let K := SplitField f
  let F := f.map (Int.castRingHom ℚ)
  let : IsSplittingField ℚ K F := IsSplittingField.splittingField F
  let : IsGalois ℚ K := IsGalois.of_separable_splitting_field hsep
  let z := tag a (Equiv.refl _) (M:K)
  let E := ℚ⟮z⟯
  have hroots (x : K) : (f.map (Int.castRingHom K)).IsRoot x ↔ ∃ i, x=a i := by
    rw [hf,root_prod]
  have hfix : E.fixingSubgroup=⊥ := by
    apply bot_unique
    intro σ hσ
    have hσz := (mem_fixingSubgroup_iff E σ).mp hσ z (mem_adjoin_simple_self ℚ z)
    have hi := fixed_of_tag σ.toRingHom a M hs (by
      intro i
      have hx := (hroots _).mpr ⟨i,rfl⟩
      have hx' := hx.map (f:=σ.toRingHom)
      rw [Polynomial.map_map,RingHom.ext_int (σ.toRingHom.comp _) (Int.castRingHom K)] at hx'
      exact (hroots _).mp hx') (Equiv.refl _) hσz
    have eq : σ.toAlgHom=AlgHom.id ℚ K := by
      apply AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet K F)
      intro x hx
      have hr := (mem_rootSet'.mp hx).2
      have hr' : (F.map (algebraMap ℚ K)).IsRoot x := by
        simpa only [IsRoot,eval_map,aeval_def] using hr
      rw [show F.map (algebraMap ℚ K)=_ from map_rat f] at hr'
      obtain ⟨i,rfl⟩ := (hroots x).mp hr'
      exact hi i
    exact Subgroup.mem_bot.mpr (AlgEquiv.ext fun x => DFunLike.congr_fun eq x)
  exact (IsGalois.fixedField_fixingSubgroup E).symm.trans (by rw [hfix,fixedField_bot])

/-- A monic irreducible whose root count at every sufficiently large prime
is the splitting indicator times the degree of the splitting field. -/
theorem separating_factor (f : ℤ[X]) (hm : f.Monic) (hn : 0<f.natDegree)
    (hs : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ h : ℤ[X], h.Monic ∧ Irreducible (h.map (algebraMap ℤ ℚ)) ∧
      h.natDegree=Module.finrank ℚ (SplitField f) ∧ ∃ B, ∀ p>B, p.Prime →
      roots h p = (h.natDegree : ℝ)*indicator f p := by
  classical
  let K := SplitField f
  let F := f.map (Int.castRingHom ℚ)
  let : IsSplittingField ℚ K F := IsSplittingField.splittingField F
  have he := map_rat (K:=K) f
  have hsplit := IsSplittingField.splits K F
  change (F.map (algebraMap ℚ K)).Splits at hsplit
  rw [he] at hsplit
  have hsep := hs.map (f:=algebraMap ℚ K)
  rw [he] at hsep
  obtain ⟨a,ha⟩ := enumerate_roots _ (hm.map _) hsplit hsep (hm.natDegree_map _)
  obtain ⟨M,_,hM⟩ := exists_separator hn a
  let R := resolvent f.natDegree M f
  let z := tag a (Equiv.refl _) (M:K)
  have hR := resolvent_factors a f ha M
  have hmon : R.Monic := (Function.Injective.monic_map_iff (f:=Int.castRingHom K)
    (by exact Int.cast_injective)).mpr (hR.symm ▸ monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have hsepR : (R.map (Int.castRingHom ℚ)).Separable := by
    apply (separable_map (algebraMap ℚ K)).mp
    rw [map_rat R]
    change ((resolvent f.natDegree M f).map (Int.castRingHom K)).Separable
    rw [hR]
    exact separable_prod_X_sub_C_iff.mpr hM
  have hz : R.aeval z=0 := by
    change R.eval₂ (Int.castRingHom K) z=0
    rw [← eval_map]
    change (R.map (Int.castRingHom K)).IsRoot z
    rw [show R.map (Int.castRingHom K)=_ from hR,root_prod]
    exact ⟨Equiv.refl _,rfl⟩
  have hi : IsIntegral ℤ z := ⟨R,hmon,hz⟩
  let h := minpoly ℤ z
  have hh : h.Monic := minpoly.monic hi
  have hdiv : h ∣ R := minpoly.isIntegrallyClosed_dvd hi hz
  have hrat : minpoly ℚ z = h.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi
  have hgen : ℚ⟮z⟯=⊤ := tag_generates hs a ha M hM
  have hdeg : h.natDegree=Module.finrank ℚ K := by
    rw [← hh.natDegree_map (algebraMap ℤ ℚ),← hrat,
      ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R:=ℚ) z),hgen,IntermediateField.finrank_top']
  have hRdeg : 0<R.natDegree := (minpoly.natDegree_pos hi).trans_le (natDegree_le_of_dvd hdiv hmon.ne_zero)
  refine ⟨h,hh,hrat ▸ minpoly.irreducible (Algebra.IsIntegral.isIntegral (R:=ℚ) z),hdeg,
    max (bad f).natAbs (bad R).natAbs,?_⟩
  intro p hp hpr
  let : Fact p.Prime := ⟨hpr⟩
  exact factor_count hm hh M p hdiv hmon
    (GapFamilies.separable_mod_above_resultant f hn.ne' hs ((le_max_left ..).trans_lt hp))
    (GapFamilies.separable_mod_above_resultant R hRdeg.ne' hsepR ((le_max_right ..).trans_lt hp))

#print axioms separating_factor
end Erdos478.SplittingDensity
