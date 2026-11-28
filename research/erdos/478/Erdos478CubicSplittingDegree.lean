import Erdos478BinaryCubicGap
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# A factor of three in the characteristic-zero splitting degree

In any number field containing all the roots, the integral factorization
reduces at every prime ideal over two. All its residue degrees are then
multiples of three at lengths 3 or 11 modulo 14. Summing local degrees
gives the divisibility in characteristic zero.
-/

namespace Erdos478.BinaryGap
open Polynomial NumberField Ideal Finset
open scoped Polynomial nonZeroDivisors
noncomputable section

private theorem integral_splits {K : Type*} [Field K] [NumberField K] {f : ℤ[X]} (hm : f.Monic)
    (hs : (f.map (Int.castRingHom K)).Splits) : (f.map (Int.castRingHom (𝓞 K))).Splits := by
  let i := algebraMap (𝓞 K) K
  have he : (f.map (Int.castRingHom (𝓞 K))).map i=f.map (Int.castRingHom K) := by
    rw [Polynomial.map_map]
    congr 1
  apply Splits.of_splits_map_of_injective (i:=i) (FaithfulSMul.algebraMap_injective _ _) (he ▸ hs)
  rw [he]
  intro x hx
  have h := (mem_roots (hm.map _).ne_zero).mp hx
  have v : IsIntegral ℤ x := ⟨f,hm,by simpa [IsRoot,aeval_def,eval_map] using h⟩
  exact ⟨⟨x,v⟩,rfl⟩

attribute [local instance] Int.ideal_span_isMaximal_of_prime

private theorem transfer (F L : Type*) [Field F] [Field L] [Algebra F L] (e : F ≃+* ZMod 2)
    (s : Bool) (m : ℕ)
    (hs : (descPochhammer L (2*(7*m+(if s then 5 else 1))+1)-1).Splits) :
    3∣Module.finrank F L := by
  let hom : ZMod 2 →+* L := (algebraMap F L).comp e.symm.toRingHom
  let : Algebra (ZMod 2) L := hom.toAlgebra
  have eq : Module.finrank F L=Module.finrank (ZMod 2) L := by
    apply Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl L)
    apply RingHom.ext
    intro x
    change algebraMap F L (e.symm (e x))=algebraMap F L x
    rw [e.symm_apply_apply]
  rw [eq]
  exact three_dvd_reduction s m hs

private theorem inertia_multiple (K : Type*) [Field K] [NumberField K] (s : Bool) (m : ℕ)
    (J : Ideal (𝓞 K)) [J.IsPrime] [J.LiesOver (span {(2:ℤ)})]
    (hs : (descPochhammer (𝓞 K) (2*(7*m+(if s then 5 else 1))+1)-1).Splits) :
    3∣J.inertiaDeg ℤ := by
  let p : Ideal ℤ := span {(2:ℤ)}
  let : p.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  have hn : p≠⊥ := by simp [p]
  let : J.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot hn J)
  let : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  let : Field ((𝓞 K) ⧸ J) := Ideal.Quotient.field J
  rw [inertiaDeg_eq_of_isMaximal p]
  apply transfer _ _ (Int.quotientSpanNatEquivZMod 2) s m
  simpa only [Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] using hs.map (Ideal.Quotient.mk J)

/-- The residue degree at every prime over two detects the cubic factor. -/
theorem three_dvd_binary_inertia (K : Type*) [Field K] [NumberField K] (s : Bool) (m : ℕ)
    (J : Ideal (𝓞 K)) [J.IsPrime] [J.LiesOver (span {(2:ℤ)})]
    (hs : (descPochhammer K (2*(7*m+(if s then 5 else 1))+1)-1).Splits) :
    3∣J.inertiaDeg ℤ := by
  classical
  let k := 2*(7*m+(if s then 5 else 1))+1
  let f := descPochhammer ℤ k-1
  have hk : 0<k := by dsimp [k]; omega
  have hD : (descPochhammer ℤ k).IsMonicOfDegree k := ⟨descPochhammer_natDegree ℤ k,monic_descPochhammer ℤ k⟩
  have hm : f.IsMonicOfDegree k := by
    simpa [f,sub_eq_add_neg] using hD.add_right (q := -(1:ℤ[X])) (by simpa using hk)
  have hsplit : (f.map (Int.castRingHom K)).Splits := by simpa [f,k] using hs
  have hi := integral_splits hm.monic hsplit
  simp only [f,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] at hi
  exact inertia_multiple K s m J hi

/-- No number field of degree prime to three contains every root of these gaps. -/
theorem three_dvd_number_field (K : Type*) [Field K] [NumberField K] (s : Bool) (m : ℕ)
    (hs : (descPochhammer K (2*(7*m+(if s then 5 else 1))+1)-1).Splits) : 3∣Module.finrank ℚ K := by
  classical
  let p : Ideal ℤ := span {(2:ℤ)}
  let : p.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  let : Fintype (p.primesOver (𝓞 K)) := (show (p.primesOver (𝓞 K)).Finite by
    rw [← IsDedekindDomain.coe_primesOverFinset (p:=p) (by simp [p]) (𝓞 K)]
    exact Finset.finite_toSet _).fintype
  rw [← RingOfIntegers.rank,← Ideal.sum_ramification_inertia_eq_finrank p]
  apply Finset.dvd_sum
  intro J _
  let := J.property.1
  let := J.property.2
  exact dvd_mul_of_dvd_right (three_dvd_binary_inertia K s m J.val hs) _

#print axioms three_dvd_binary_inertia
#print axioms three_dvd_number_field
end
end Erdos478.BinaryGap
