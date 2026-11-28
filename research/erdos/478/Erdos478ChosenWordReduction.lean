import Erdos478ChosenSpecialization
import Erdos478JointRootBound

/-!
# Prime-field reductions of a prescribed root word

Taking a modular root of the minimal polynomial of a chosen word value
keeps the chosen coordinates in one residue field. If the word polynomial
remains separable, its injective encoding forces Frobenius to fix each
coordinate of that particular word.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

private theorem root_iff_entry {K I : Type*} [Field K] [Fintype I] (b : I → K) (x : K) :
    (∏ i, (X-C (b i))).IsRoot x ↔ ∃ i, x = b i := by
  classical
  simp [IsRoot.def,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

/-- Every entry of the prescribed word is an integer modulo a single maximal
ideal over the chosen prime. The same reduction applies to all the root lists. -/
theorem chosen_word_reduction {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    [Algebra.IsIntegral ℤ S] {n : ℕ} (d : Fin n → ℕ) (f : Fin n → ℤ[X])
    (a : (i : Fin n) → Fin (d i) → S)
    (hf : ∀ i, (f i).map (Int.castRingHom S) = ∏ j, (X-C (a i j)))
    (M : ℕ) (t : Word d) {p : ℕ} [Fact p.Prime]
    (hs : ((wordPolynomial n f d (M:ℤ)).map (Int.castRingHom (ZMod p))).Separable)
    (z : ZMod p) (hz : ((minpoly ℤ (wordValue (M:S) (fun i => a i (t i)))).map
      (Int.castRingHom (ZMod p))).IsRoot z) :
    ∃ Q : Ideal S, Q.IsMaximal ∧ (p:S) ∈ Q ∧
      ∀ i, ∃ m : ℤ, a i (t i) - (m:S) ∈ Q := by
  classical
  let x := wordValue (M:S) (fun i => a i (t i))
  obtain ⟨Q,hQ,hp,hx⟩ := specialize_chosen_root x z hz
  let K := S ⧸ Q
  let : Field K := Ideal.Quotient.field Q
  let ρ := Ideal.Quotient.mk Q
  let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by simpa [ρ] using (Ideal.Quotient.eq_zero_iff_mem.mpr hp))
  let j := ZMod.castHom (dvd_refl p) K
  let b (i : Fin n) (l : Fin (d i)) : K := ρ (a i l)
  have lift (P : ℤ[X]) : (P.map (Int.castRingHom (ZMod p))).map j = P.map (Int.castRingHom K) := by
    rw [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom K)]
  have hb (i : Fin n) : (f i).map (Int.castRingHom K) = ∏ l, (X-C (b i l)) := by
    have he := congrArg (Polynomial.map ρ) (hf i)
    simpa only [Polynomial.map_map,RingHom.ext_int (ρ.comp _) (Int.castRingHom K),
      Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C] using he
  let W := wordPolynomial n f d (M:ℤ)
  have hw : W.map (Int.castRingHom K) =
      ∏ u : Word d, (X-C (wordValue (M:K) (fun i => b i (u i)))) := by
    rw [show W = wordPolynomial n f d (M:ℤ) from rfl,wordPolynomial_map]
    simp_rw [hb]
    simpa using wordPolynomial_factors d b (M:K)
  have hsep : (W.map (Int.castRingHom K)).Separable := lift W ▸ hs.map (f := j)
  rw [hw] at hsep
  have htag : wordValue (M:K) (fun i => b i (t i)) = (z.val:K) := by
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [map_sub,sub_eq_zero,map_natCast] at he
    simpa only [x,wordValue,b,ρ,map_sum,map_mul,map_pow,map_natCast] using he
  let φ := frobenius K p
  have htagfix : φ (wordValue (M:K) (fun i => b i (t i))) =
      wordValue (M:K) (fun i => b i (t i)) := by rw [htag,map_natCast]
  have hc (i l) : ∃ k, φ (b i l) = b i k := by
    have hr : ((f i).map (Int.castRingHom K)).IsRoot (b i l) := by
      rw [hb,root_iff_entry]
      exact ⟨l,rfl⟩
    have he := hr.map (f := φ)
    rwa [Polynomial.map_map,RingHom.ext_int (φ.comp _) (Int.castRingHom K),hb,root_iff_entry] at he
  have fixed := fixed_word d b φ M hc hsep.injective_of_prod_X_sub_C t htagfix
  refine ⟨Q,hQ,hp,?_⟩
  intro i
  have hpow : (b i (t i))^p = b i (t i) := fixed i
  obtain ⟨m,hm⟩ := (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr hpow)
  refine ⟨m,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub,map_intCast,sub_eq_zero]
  exact hm.symm

#print axioms chosen_word_reduction

end Erdos478.EffectiveResolvent
