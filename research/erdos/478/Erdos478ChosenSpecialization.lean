import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Finite.Basic

/-!
# Specializing a chosen algebraic integer at a modular root

A root of the minimal polynomial in the prime field gives a maximal ideal
of the monogenic order. Lying over preserves that root value when all the
other integral elements are reduced in a single residue field.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial

theorem specialize_chosen_root {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    [Algebra.IsIntegral ℤ S] (x : S) {p : ℕ} [Fact p.Prime] (z : ZMod p)
    (hz : ((minpoly ℤ x).map (Int.castRingHom (ZMod p))).IsRoot z) :
    ∃ Q : Ideal S, Q.IsMaximal ∧ (p:S)∈Q ∧ x-(z.val:S)∈Q := by
  classical
  let A := Algebra.adjoin ℤ ({x} : Set S)
  have hi := Algebra.IsIntegral.isIntegral (R := ℤ) x
  let e := minpoly.equivAdjoin hi
  have hz' : (minpoly ℤ x).eval₂ (Int.castRingHom (ZMod p)) z = 0 := by
    simpa only [IsRoot.def,eval_map] using hz
  let ev := AdjoinRoot.lift (Int.castRingHom (ZMod p)) z hz'
  let φ : A →+* ZMod p := ev.comp e.symm.toRingHom
  let u : A := e (AdjoinRoot.root (minpoly ℤ x))
  have ux : (u:S)=x := by simp [u,e,minpoly.coe_equivAdjoin,AdjoinRoot.Minpoly.toAdjoin]
  have hu : φ u=z := by simp [φ,u,ev,AdjoinRoot.lift_root]
  have surj : Function.Surjective φ := by
    intro a
    obtain ⟨n,rfl⟩ := ZMod.intCast_surjective a
    exact ⟨(n:A),map_intCast ..⟩
  have : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ surj
  have : Algebra.IsIntegral A S := ⟨fun y => (Algebra.IsIntegral.isIntegral (R := ℤ) y).tower_top⟩
  obtain ⟨Q,hQ,hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (RingHom.ker φ)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap A S) from Subtype.val_injective)]; exact bot_le)
  have pull (a : A) (h : φ a=0) : (a:S)∈Q := by
    apply (Ideal.mem_comap (f := algebraMap A S)).mp
    rw [hc]
    exact RingHom.mem_ker.mpr h
  refine ⟨Q,hQ,?_,?_⟩
  · exact_mod_cast pull (p:A) (by simp)
  · have h := pull (u-(z.val:A)) (by simp [hu])
    simpa only [Subalgebra.coe_sub,show ((↑(z.val:A)):S)=(z.val:S) from rfl,ux] using h

#print axioms specialize_chosen_root

end Erdos478.EffectiveResolvent
