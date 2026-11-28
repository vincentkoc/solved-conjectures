import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! # Simultaneous lifting of the residue Frobenius at a rational prime -/

namespace Erdos478.LocalWitness
open NumberField Ideal Polynomial
noncomputable section
attribute [local instance] Int.ideal_span_isMaximal_of_prime

def residueEmbedding {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) [J.LiesOver (span {(p:ℤ)})] : ZMod p →+* (𝓞 K) ⧸ J :=
  (algebraMap (ℤ ⧸ span {(p:ℤ)}) ((𝓞 K) ⧸ J)).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom

/-- One characteristic-zero automorphism induces the p-th power on reductions
of every algebraic integer. No unramified hypothesis on the whole extension is required. -/
theorem residue_lift (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] (p : ℕ) [hpr : Fact p.Prime]
    (J : Ideal (𝓞 K)) [J.IsMaximal] [J.LiesOver (span {(p:ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, ∀ z : 𝓞 K, Ideal.Quotient.mk J (σ • z)=(Ideal.Quotient.mk J z)^p := by
  classical
  let P := span {(p:ℤ)}
  let : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hn : P≠⊥ := by simp [P,hpr.out.ne_zero]
  have hJ := Ideal.ne_bot_of_liesOver_of_ne_bot hn J
  let : Finite ((𝓞 K) ⧸ J) := (Ideal.absNorm_ne_zero_iff J).mp (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  let : Field (ℤ ⧸ P) := Ideal.Quotient.field P
  let : Field ((𝓞 K) ⧸ J) := Ideal.Quotient.field J
  let e := Int.quotientSpanNatEquivZMod p
  let : Fintype (ℤ ⧸ P) := Fintype.ofEquiv _ e.symm.toEquiv
  have hcard : Fintype.card (ℤ ⧸ P)=p := (Fintype.card_congr e.toEquiv).trans (ZMod.card p)
  let G := K ≃ₐ[ℚ] K
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ P) ((𝓞 K) ⧸ J)
  obtain ⟨s,hs⟩ := Ideal.Quotient.stabilizerHom_surjective G P J φ
  refine ⟨s.val,fun z => ?_⟩
  have eq := DFunLike.congr_fun hs (Ideal.Quotient.mk J z)
  rw [Ideal.Quotient.stabilizerHom_apply,FiniteField.frobeniusAlgEquivOfAlgebraic_apply,hcard] at eq
  exact eq

/-- The p-th power fixes precisely the embedded prime field. -/
theorem pow_fixed_iff {p : ℕ} [hpr : Fact p.Prime] {R : Type*} [Field R] (ι : ZMod p →+* R) (x : R) :
    x^p=x ↔ ∃ a : ZMod p, ι a=x := by
  classical
  let P : (ZMod p)[X] := X^p-X
  have roots : P.roots=Finset.univ.val := by simpa [P] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have nonzero : (X^p-X : R[X])≠0 := FiniteField.X_pow_card_sub_X_ne_zero R hpr.out.one_lt
  have full : P.roots.card=P.natDegree := by
    rw [roots,← Finset.card_def,Finset.card_univ,ZMod.card]
    exact (FiniteField.X_pow_card_sub_X_natDegree_eq _ hpr.out.one_lt).symm
  have eq := roots_map_of_injective_of_card_eq_natDegree ι.injective full
  rw [roots,show P.map ι=(X^p-X : R[X]) by simp [P]] at eq
  constructor
  · intro hx
    have hmem : x∈(X^p-X : R[X]).roots := (mem_roots nonzero).mpr (by simp [IsRoot.def,hx])
    obtain ⟨a,_,ha⟩ := Multiset.mem_map.mp (eq.symm ▸ hmem)
    exact ⟨a,ha⟩
  · rintro ⟨a,rfl⟩
    rw [← map_pow,ZMod.pow_card]

#print axioms residueEmbedding
#print axioms residue_lift
#print axioms pow_fixed_iff
end
end Erdos478.LocalWitness
