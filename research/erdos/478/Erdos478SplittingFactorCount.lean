import Erdos478EffectiveSplitting
import Erdos478CoprimeRootMoments

/-!
# Counting complete splitting with an irreducible resolvent factor

At a prime of separable reduction, a root of any factor of a separating
permutation resolvent forces complete splitting of the input. Conversely,
complete splitting makes every root of the factor rational.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset Filter Topology EffectiveResolvent RootMoments
open scoped Classical

noncomputable def indicator (f : ℤ[X]) (p : ℕ) : ℝ :=
  if (f.map (Int.castRingHom (ZMod p))).Splits then 1 else 0

private theorem root_card (h : ℤ[X]) (hh : h.Monic) (p : ℕ) [Fact p.Prime] :
    roots h p = (((h.map (Int.castRingHom (ZMod p))).roots.toFinset.card : ℕ) : ℝ) := by
  classical
  let H := h.map (Int.castRingHom (ZMod p))
  have hn : H≠0 := (hh.map _).ne_zero
  let e : RootPairs.solutions h (ZMod p) ≃ H.roots.toFinset :=
    Equiv.subtypeEquivRight fun x => by simp [H,mem_roots hn,IsRoot,eval_map]
  change (Nat.card _ : ℝ)=(H.roots.toFinset.card : ℝ)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem factor_count {f h : ℤ[X]} (hf : f.Monic) (hh : h.Monic) (M p : ℕ) [Fact p.Prime]
    (hd : h ∣ resolvent f.natDegree M f)
    (hR : (resolvent f.natDegree M f).Monic)
    (hs : (f.map (Int.castRingHom (ZMod p))).Separable)
    (hr : ((resolvent f.natDegree M f).map (Int.castRingHom (ZMod p))).Separable) :
    roots h p = (h.natDegree : ℝ)*indicator f p := by
  classical
  let φ := Int.castRingHom (ZMod p)
  let H := h.map φ
  let R := (resolvent f.natDegree M f).map φ
  have hdiv : H ∣ R := Polynomial.map_dvd φ hd
  have hsep : H.Separable := hr.of_dvd hdiv
  have hne : H≠0 := (hh.map φ).ne_zero
  by_cases hsplit : (f.map φ).Splits
  · obtain ⟨a,ha⟩ := enumerate_roots (f.map φ) (hf.map φ) hsplit hs (hf.natDegree_map φ)
    have hrs : R.Splits := by
      change ((resolvent f.natDegree M f).map φ).Splits
      rw [resolvent_factors a f ha M]
      exact Splits.prod fun _ _ => Splits.X_sub_C _
    have hhs := hrs.of_dvd (hR.map φ).ne_zero hdiv
    rw [root_card h hh p]
    change (H.roots.toFinset.card : ℝ) = _
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep),← hhs.natDegree_eq_card_roots,hh.natDegree_map]
    simp [indicator,show (f.map (Int.castRingHom (ZMod p))).Splits from hsplit]
  · have hem : H.roots.toFinset=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hroot := (mem_roots hne).mp (Multiset.mem_toFinset.mp hz)
      have hroot' : R.IsRoot z := by
        obtain ⟨g,hg⟩ := hdiv
        rw [hg]
        simp [Polynomial.IsRoot,show H.eval z=0 from hroot]
      exact hsplit (split_of_resolvent_root f hf M p hs hr ⟨z,hroot'⟩)
    rw [root_card h hh p]
    change (H.roots.toFinset.card : ℝ)=_
    simp [hem,indicator,show ¬(f.map (Int.castRingHom (ZMod p))).Splits from hsplit]

#print axioms factor_count
end Erdos478.SplittingDensity
