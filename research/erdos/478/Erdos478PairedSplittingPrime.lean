import Erdos478ChosenWordPrime
import Erdos478ChosenGapPairs

/-!
# Effective complete splitting of families with reflected roots

One word coordinate per reflection pair suffices. Reducing the chosen
representatives into the prime field reduces their partners there as well,
so all original factors split completely.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

private theorem split_from_integral_residues {S I : Type*} [CommRing S] [Fintype I]
    (f : ℤ[X]) (a : I → S) (hf : f.map (Int.castRingHom S) = ∏ l, (X-C (a l)))
    {p : ℕ} [Fact p.Prime] (Q : Ideal S) [Q.IsMaximal] (hp : (p:S) ∈ Q)
    (hr : ∀ l, ∃ m : ℤ, a l-(m:S) ∈ Q) : (f.map (Int.castRingHom (ZMod p))).Splits := by
  classical
  let K := S ⧸ Q
  let : Field K := Ideal.Quotient.field Q
  let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hp))
  let j := ZMod.castHom (dvd_refl p) K
  let ρ := Ideal.Quotient.mk Q
  choose m hm using hr
  have he (l : I) : ρ (a l) = (m l : K) := by
    simpa only [map_sub,map_intCast,sub_eq_zero] using (Ideal.Quotient.eq_zero_iff_mem.mpr (hm l))
  have hh : f.map (Int.castRingHom (ZMod p)) = ∏ l, (X-C (m l:ZMod p)) := by
    apply Polynomial.map_injective j j.injective
    have h := congrArg (Polynomial.map ρ) hf
    simp only [Polynomial.map_map,RingHom.ext_int (ρ.comp _) (Int.castRingHom K),
      Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,he] at h
    simpa only [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom K),
      Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,show ∀ l, j (m l:ZMod p) = (m l:K) from fun l => map_intCast j (m l)] using h
  rw [hh]
  exact Splits.prod (fun _ _ => Splits.X_sub_C _)

/-- Each input polynomial has an even number of roots and each pair sums
to the prescribed integer. The word degree bound counts one representative
per pair, and the selected prime splits the entire family. -/
theorem paired_splitting_prime {I : Type} [Fintype I] (r : I → ℕ)
    (hn : 0 < Fintype.card (Σ i, Fin (r i))) (f : I → ℤ[X])
    (a : (i : I) → Fin (2*r i) ↪ ℂ)
    (hf : ∀ i, (f i).map (Int.castRingHom ℂ) = ∏ l, (X-C (a i l)))
    (v : (i : I) → Fin (r i) × Bool ≃ Fin (2*r i)) (center : I → ℤ)
    (hv : ∀ i k, a i (v i (k,true)) = (center i:ℂ)-a i (v i (k,false)))
    (method : RootPrimeBound) (U B : ℕ) (hU : 0<U) (hB : 0<B)
    (hr : ∀ i l, ‖a i l‖ ≤ U) :
    let N := Fintype.card (Σ i, Fin (r i))
    let D := ∏ i, (2*r i)^(r i)
    let V := wordBound N D U
    ∃ e ≤ D, ∃ p ≤ method.bound e V (B*(2*V)^(D^2)), p.Prime ∧ ¬p ∣ B ∧
      ∀ i, ((f i).map (Int.castRingHom (ZMod p))).Splits := by
  classical
  let O := integralClosure ℤ ℂ
  let j := O.val.toRingHom
  have hj : Function.Injective j := Subtype.val_injective
  have hm (i) : (f i).Monic := (Function.Injective.monic_map_iff (f := Int.castRingHom ℂ)
    Int.cast_injective).mpr (hf i ▸ monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have hi (i l) : IsIntegral ℤ (a i l) := by
    refine ⟨f i,hm i,?_⟩
    change (f i).eval₂ (Int.castRingHom ℂ) (a i l) = 0
    rw [← eval_map,hf,eval_prod]
    exact Finset.prod_eq_zero (mem_univ l) (by simp)
  let b (i : I) : Fin (2*r i) ↪ O := ⟨fun l => ⟨a i l,hi i l⟩,
    fun _ _ h => (a i).injective (congrArg Subtype.val h)⟩
  have hb (i) : (f i).map (Int.castRingHom O) = ∏ l, (X-C (b i l)) := by
    apply Polynomial.map_injective j hj
    simpa only [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom ℂ),
      Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,show ∀ i l, j (b i l) = a i l from fun _ _ => rfl] using hf i
  let T := Σ i, Fin (r i)
  let N := Fintype.card T
  let E := (Fintype.equivFin T).symm
  let d (l : Fin N) := 2*r (E l).1
  let t (l : Fin N) : Fin (d l) := v (E l).1 ((E l).2,false)
  have hD : Fintype.card (Word d) = ∏ i, (2*r i)^(r i) := by
    change Fintype.card ((l : Fin N) → Fin (d l)) = _
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    calc ∏ l, d l = ∏ x : T, 2*r x.1 := Fintype.prod_equiv E _ _ (fun _ => rfl)
         _ = _ := by rw [Fintype.prod_sigma]; simp
  obtain ⟨e,he,p,hp,hprime,havoid,Q,hQ,hpQ,hentry⟩ := chosen_prime_with j hj method hn d
    (fun l => f (E l).1) (fun l => b (E l).1) (fun l => hb (E l).1) t U B hU hB
    (fun l k => hr (E l).1 k)
  rw [hD] at he hp
  let : Fact p.Prime := ⟨hprime⟩
  refine ⟨e,he,p,hp,hprime,havoid,fun i => split_from_integral_residues (f i) (b i) (hb i) Q hpQ ?_⟩
  have base (y : T) : ∃ m : ℤ, b y.1 (v y.1 (y.2,false))-(m:O) ∈ Q := by
    obtain ⟨l,rfl⟩ := E.surjective y
    exact hentry l
  intro l
  obtain ⟨⟨k,c⟩,rfl⟩ := (v i).surjective l
  obtain ⟨m,hm⟩ := base ⟨i,k⟩
  cases c with
  | false => exact ⟨m,hm⟩
  | true =>
    have pair : b i (v i (k,true)) = (center i:O)-b i (v i (k,false)) := Subtype.ext (hv i k)
    refine ⟨center i-m,?_⟩
    rw [pair,Int.cast_sub,show (center i:O)-b i (v i (k,false))-((center i:O)-m) = -(b i (v i (k,false))-(m:O)) by ring]
    exact Q.neg_mem hm

#print axioms paired_splitting_prime

end Erdos478.EffectiveResolvent
