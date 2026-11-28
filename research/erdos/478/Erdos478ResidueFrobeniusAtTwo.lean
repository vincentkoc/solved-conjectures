import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# A lift of the binary residue-field Frobenius

At any prime ideal above two in a finite Galois number field, lift
the squaring automorphism from the residue field. Its lift has order
divisible by the residue degree. Every integral point fixed by this
lift reduces to zero or one.
-/

namespace Erdos478.BinaryGap
open NumberField Ideal
noncomputable section

attribute [local instance] Int.ideal_span_isMaximal_of_prime

theorem binary_frobenius_lift (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (J : Ideal (𝓞 K)) [J.IsPrime] [J.LiesOver (span {(2:ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, J.inertiaDeg ℤ∣orderOf σ ∧
      ∀ z : 𝓞 K, σ (z:K)=(z:K) → Ideal.Quotient.mk J z=0 ∨ Ideal.Quotient.mk J z=1 := by
  classical
  let P := span {(2:ℤ)}
  let : P.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  have hn : P≠⊥ := by simp [P]
  have hJ := Ideal.ne_bot_of_liesOver_of_ne_bot hn J
  let : J.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hJ
  let : Finite ((𝓞 K) ⧸ J) := (Ideal.absNorm_ne_zero_iff J).mp (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  let : Field (ℤ ⧸ P) := Ideal.Quotient.field P
  let : Field ((𝓞 K) ⧸ J) := Ideal.Quotient.field J
  let e := Int.quotientSpanNatEquivZMod 2
  let : Fintype (ℤ ⧸ P) := Fintype.ofEquiv _ e.symm.toEquiv
  have hcard : Fintype.card (ℤ ⧸ P)=2 := (Fintype.card_congr e.toEquiv).trans (ZMod.card 2)
  let G := K ≃ₐ[ℚ] K
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ P) ((𝓞 K) ⧸ J)
  obtain ⟨s,hs⟩ := Ideal.Quotient.stabilizerHom_surjective G P J φ
  refine ⟨s.val,?_,?_⟩
  · rw [inertiaDeg_eq_of_isMaximal P]
    have ord : orderOf φ=Module.finrank (ℤ ⧸ P) ((𝓞 K) ⧸ J) := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic ..
    rw [← ord,← hs,Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ s
  · intro z hz
    have fixed : s • z=z := Subtype.ext hz
    have h := DFunLike.congr_fun hs (Ideal.Quotient.mk J z)
    rw [Ideal.Quotient.stabilizerHom_apply,fixed,FiniteField.frobeniusAlgEquivOfAlgebraic_apply,hcard] at h
    exact eq_zero_or_one_of_sq_eq_self h.symm

#print axioms binary_frobenius_lift
end
end Erdos478.BinaryGap
