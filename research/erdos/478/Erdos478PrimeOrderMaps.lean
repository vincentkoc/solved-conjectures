import Erdos478RootPairOrder
import Erdos478PrimeIdealMass
import Mathlib.RingTheory.ZMod

/-!
# Specializations of orders into a prime field

The kernel of a specialization of the ring of integers has residue degree one
and determines the specialization. A full-rank suborder has the same
specializations away from the primes dividing its additive index.
-/

namespace Erdos478.RootPairs
noncomputable section

open NumberField Ideal Finset MeanDeficit Module

private theorem ker_injective {A : Type*} [CommRing A] (p : ℕ) :
    Function.Injective (RingHom.ker : (A →+* ZMod p) → Ideal A) := by
  intro f g he
  ext x
  obtain ⟨n,hn⟩ := ZMod.intCast_surjective (f x)
  have hx : x - (n:A) ∈ RingHom.ker f := by simpa [RingHom.mem_ker] using sub_eq_zero.mpr hn.symm
  rw [he,RingHom.mem_ker,map_sub,map_intCast,sub_eq_zero] at hx
  exact hn.symm.trans hx.symm

private def kernelEmbedding (K : Type*) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    (𝓞 K →+* ZMod p) ↪ {P : Ideal (𝓞 K) // P ∈ (abovePrime K p).filter (fun J => J.inertiaDeg ℤ = 1)} := by
  classical
  refine ⟨fun f => ⟨RingHom.ker f,?_⟩,fun _ _ h => ker_injective p (congrArg Subtype.val h)⟩
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨n,hn⟩ := ZMod.intCast_surjective x
    exact ⟨(n:𝓞 K),(map_intCast f n).trans hn⟩
  have hP : RingHom.ker f ∈ abovePrime K p := by
    apply (mem_over hp.out _).mpr
    refine ⟨RingHom.ker_isPrime f,⟨?_⟩⟩
    change Ideal.span {(p:ℤ)} = RingHom.ker (f.comp (algebraMap ℤ (𝓞 K)))
    rw [RingHom.ext_int (f.comp _) (Int.castRingHom (ZMod p)),ZMod.ker_intCastRingHom]
  have he := RingHom.quotientKerEquivOfSurjective (f := f) hs
  have hn : absNorm (RingHom.ker f) = p := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_congr he.toEquiv,Nat.card_zmod]
  refine mem_filter.mpr ⟨hP,?_⟩
  have hpow := (norm_over hp.out hP).1.symm.trans hn
  exact Nat.pow_right_injective hp.out.one_lt ((hpow.trans (pow_one _).symm))

private theorem kernel_surjective (K : Type*) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    Function.Surjective (kernelEmbedding K p) := by
  classical
  rintro ⟨P,hP⟩
  obtain ⟨hAbove,hdeg⟩ := mem_filter.mp hP
  have hn := (norm_over hp.out hAbove).1
  rw [hdeg,pow_one,Ideal.absNorm_apply,Submodule.cardQuot_apply] at hn
  let : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (hn.trans_ne hp.out.ne_zero)
  let : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  let e := (ZMod.ringEquivOfPrime _ hp.out (Nat.card_eq_fintype_card.symm.trans hn)).symm
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk P),Subtype.ext ?_⟩
  change RingHom.ker (e.toRingHom.comp _) = P
  rw [RingHom.ker_comp_of_injective _ e.injective,Ideal.mk_ker]

/-- Away from a finite cutoff, the maps from a full-rank order into the prime
field correspond exactly to the degree-one prime ideals in its number field. -/
theorem order_maps_count {A : Type*} [CommRing A] (K : Type*) [Field K] [NumberField K]
    (j : A →+* 𝓞 K) (hj : Function.Injective j) (hr : finrank ℤ A = finrank ℚ K) :
    ∃ B : ℕ, ∀ p > B, p.Prime → Nat.card (A →+* ZMod p) = linearCount K p := by
  classical
  let S := j.range
  let e : A ≃+* S := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ h => hj (congrArg Subtype.val h),j.rangeRestrict_surjective⟩
  let H := S.toAddSubgroup
  have hR : finrank ℤ H.toIntSubmodule = finrank ℤ (𝓞 K) := by
    rw [RingOfIntegers.rank,← hr]
    exact e.toIntAlgEquiv.toLinearEquiv.finrank_eq.symm
  let : Finite ((𝓞 K) ⧸ H) := Submodule.finiteQuotientOfFreeOfRankEq H.toIntSubmodule hR
  have hd : 0 < H.index := by rw [AddSubgroup.index_eq_card]; exact Nat.card_pos
  refine ⟨H.index,?_⟩
  intro p hB hp
  let : Fact p.Prime := ⟨hp⟩
  let k := ZMod p
  let kerMap := kernelEmbedding K p
  let : Finite (𝓞 K →+* k) := Finite.of_injective kerMap kerMap.injective
  have hnz : (H.index : k) ≠ 0 := fun he => Nat.not_dvd_of_pos_of_lt hd hB ((ZMod.natCast_eq_zero_iff ..).mp he)
  have hres : Function.Surjective (fun ψ : 𝓞 K →+* k => ψ.comp j) := by
    intro φ
    obtain ⟨ψ,hψ⟩ := extend_order S H.index
      hnz
      (fun x => show (H.index : 𝓞 K)*x ∈ H by simpa only [nsmul_eq_mul] using H.nsmul_index_mem x)
      (φ.comp e.symm.toRingHom)
    refine ⟨ψ,RingHom.ext fun x => ?_⟩
    exact (DFunLike.congr_fun hψ (e x)).trans (congrArg φ (e.symm_apply_apply x))
  have hinj : Function.Injective (fun ψ : 𝓞 K →+* k => ψ.comp j) := by
    intro ψ χ he
    ext x
    have hx := H.nsmul_index_mem x
    rw [nsmul_eq_mul] at hx
    obtain ⟨a,ha⟩ := (show (H.index : 𝓞 K)*x ∈ j.range from hx)
    have ht := DFunLike.congr_fun he a
    change ψ (j a) = χ (j a) at ht
    rw [ha,map_mul,map_mul,map_natCast,map_natCast] at ht
    exact mul_left_cancel₀ hnz ht
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj,hres⟩)]
  exact (Nat.card_congr (Equiv.ofBijective kerMap ⟨kerMap.injective,kernel_surjective K p⟩)).trans
    (by simp only [Nat.card_eq_fintype_card,Fintype.card_coe,linearCount])

#print axioms order_maps_count

end
end Erdos478.RootPairs
