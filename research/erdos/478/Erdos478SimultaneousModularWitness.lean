import Erdos478ResidueRootCounts
import Erdos478GaloisObservables

/-! # A single Galois witness for every regular root count at a prime -/

namespace Erdos478.LocalWitness
open Polynomial NumberField Ideal FrobeniusCounts RootMoments MulAction
noncomputable section
open scoped Classical
attribute [local instance] Int.ideal_span_isMaximal_of_prime

private def fieldRoots (K : Type*) [Field K] [Algebra ℚ K] (f : ℤ[X]) :
    rootType K f ≃ Roots (f.map (Int.castRingHom K)) :=
  Equiv.subtypeEquivRight fun x => by
    simp only [rootType,rootSet_def,Finset.mem_coe,aroots_def,map_integer_poly]

private theorem field_fixed (K : Type*) [Field K] [Algebra ℚ K] (f : ℤ[X]) (σ : Aut K) :
    fixed K f σ=Nat.card {x : Roots (f.map (Int.castRingHom K)) // σ x.val=x.val} := by
  unfold fixed fixedCount
  apply Nat.card_congr
  apply (fieldRoots K f).subtypeEquiv
  intro x
  change σ • x=x ↔ σ x.val=x.val
  exact Subtype.ext_iff

private theorem mod_count (p : ℕ) [Fact p.Prime] (f : ℤ[X]) (hm : f.Monic) :
    primeRoots f p=Nat.card (Roots (f.map (Int.castRingHom (ZMod p)))) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  simp [mem_roots (hm.map _).ne_zero,IsRoot,eval_map]

/-- The same lift works for all monic split integer polynomials with separable
reductions, even if another part of the ambient number field ramifies at p. -/
theorem simultaneous_witness (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) [hpr : Fact p.Prime] :
    ∃ σ : Aut K, ∀ f : ℤ[X], f.Monic → (f.map (Int.castRingHom K)).Separable →
      (f.map (Int.castRingHom K)).Splits → (f.map (Int.castRingHom (ZMod p))).Separable →
      fixed K f σ=primeRoots f p := by
  classical
  let P : Ideal ℤ := span {(p:ℤ)}
  let : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨J,hJ,hcomp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S:=𝓞 K) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]; exact bot_le)
  let : J.IsMaximal := hJ
  let : J.LiesOver P := ⟨hcomp.symm⟩
  obtain ⟨σ,hs⟩ := residue_lift K p J
  exact ⟨σ,fun f hm sep sp reg => (field_fixed K f σ).trans
    ((residue_fixed_count K p J σ hs f hm sep sp reg).trans (mod_count p f hm).symm)⟩

#print axioms simultaneous_witness
end
end Erdos478.LocalWitness
