import Erdos478ChosenWordReduction

/-!
# Bounded primes for a prescribed word of algebraic integers

Use the minimal polynomial of the chosen word value to select its Galois
orbit. Its degree and the norms of its roots are bounded by those of the
full word polynomial.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

private theorem prod_root_iff {K I : Type*} [Field K] [Fintype I] (a : I → K) (x : K) :
    (∏ i, (X-C (a i))).IsRoot x ↔ ∃ i, x = a i := by
  classical
  simp [IsRoot.def,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

/-- Schur selection may be restricted to a monic nonconstant factor without
increasing the complex root bound or the allowed degree. -/
theorem bounded_factor_prime (method : RootPrimeBound) {I : Type} [Fintype I]
    (W g : ℤ[X]) (a : I ↪ ℂ) (hw : W.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i)))
    (hg : g.Monic) (hd : 0 < g.natDegree) (hdiv : g ∣ W)
    (U B : ℕ) (hB : 0<B) (hU : ∀ i, ‖a i‖ ≤ U) :
    g.natDegree ≤ Fintype.card I ∧
      ∃ p ≤ method.bound g.natDegree U B, p.Prime ∧ ¬p ∣ B ∧
        ∃ z : ZMod p, (g.map (Int.castRingHom (ZMod p))).IsRoot z := by
  classical
  let j := Int.castRingHom ℂ
  have hv : g.map j ∣ W.map j := Polynomial.map_dvd j hdiv
  have hws : (W.map j).Separable := hw ▸ separable_prod_X_sub_C_iff.mpr a.injective
  have hwm : (W.map j).Monic := hw ▸ monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hwn : (W.map j).natDegree = Fintype.card I := by rw [hw]; simp
  obtain ⟨b,he⟩ := enumerate_roots (g.map j) (hg.map j) (IsAlgClosed.splits _)
    (hws.of_dvd hv) (hg.natDegree_map j)
  have hb (i : Fin g.natDegree) : ‖b i‖ ≤ U := by
    have hr : (g.map j).IsRoot (b i) := by rw [he,prod_root_iff]; exact ⟨i,rfl⟩
    have hh := hr.dvd hv
    rw [hw,prod_root_iff] at hh
    obtain ⟨k,hk⟩ := hh
    simpa only [hk] using hU k
  have : Nonempty (Fin g.natDegree) := ⟨⟨0,hd⟩⟩
  constructor
  · rw [← hg.natDegree_map j,← hwn]
    exact natDegree_le_of_dvd hv hwm.ne_zero
  · simpa only [Fintype.card_fin] using method.prime_root g b he U B hB hb

/-- A bounded prime simultaneously specializes the selected coordinates.
The Schur degree is at most the number of words, even when several
coordinates come from the same polynomial. -/
theorem chosen_prime_with {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    [Algebra.IsIntegral ℤ S] (j : S →+* ℂ) (hj : Function.Injective j)
    (method : RootPrimeBound) {n : ℕ} (hn : 0<n) (d : Fin n → ℕ)
    (f : Fin n → ℤ[X]) (a : (i : Fin n) → Fin (d i) ↪ S)
    (hf : ∀ i, (f i).map (Int.castRingHom S) = ∏ l, (X-C (a i l)))
    (t : Word d) (U B : ℕ) (hU : 0<U) (hB : 0<B) (hr : ∀ i l, ‖j (a i l)‖ ≤ U) :
    let D := Fintype.card (Word d)
    let V := wordBound n D U
    ∃ e ≤ D, ∃ p ≤ method.bound e V (B*(2*V)^(D^2)), p.Prime ∧ ¬p ∣ B ∧
      ∃ Q : Ideal S, Q.IsMaximal ∧ (p:S) ∈ Q ∧ ∀ i, ∃ m : ℤ, a i (t i)-(m:S) ∈ Q := by
  classical
  let D := Fintype.card (Word d)
  let V := wordBound n D U
  let b (i : Fin n) : Fin (d i) ↪ ℂ := (a i).trans ⟨j,hj⟩
  have hb (i : Fin n) : (f i).map (Int.castRingHom ℂ) = ∏ l, (X-C (b i l)) := by
    change (f i).map (Int.castRingHom ℂ) = ∏ l, (X-C (j (a i l)))
    have h := congrArg (Polynomial.map j) (hf i)
    simpa only [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom ℂ),
      Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C] using h
  obtain ⟨M,hM,hsep⟩ := word_separator hn d b
  let c : Word d ↪ ℂ := ⟨fun u => wordValue (M:ℂ) (fun i => b i (u i)),hsep⟩
  let W := wordPolynomial n f d (M:ℤ)
  have hw : W.map (Int.castRingHom ℂ) = ∏ u, (X-C (c u)) := by
    rw [show W = wordPolynomial n f d (M:ℤ) from rfl,wordPolynomial_map]
    simp_rw [hb]
    simpa [c] using wordPolynomial_factors d (fun i => b i) (M:ℂ)
  have hc (u : Word d) : ‖c u‖ ≤ V := by
    have he := tag_norm (fun i => b i (u i)) (fun i => hr i (u i)) (M := M) (Equiv.refl _)
    have he' : ‖c u‖ ≤ (n*U*(M+1)^n : ℕ) := by
      simpa [c,tag,Polynomial.ofFn_eq_sum_monomial,eval_finsetSum,wordValue,mul_comm,Function.comp_def] using he
    apply he'.trans
    exact_mod_cast (by dsimp [V,D,wordBound]; gcongr : n*U*(M+1)^n ≤ V)
  let x := wordValue (M:S) (fun i => a i (t i))
  let g := minpoly ℤ x
  have hx : j x = c t := by simp only [x,wordValue,map_sum,map_mul,map_pow,map_natCast]; rfl
  have hv : W.aeval x = 0 := by
    apply hj
    change j (W.eval₂ (Int.castRingHom S) x) = j 0
    rw [hom_eval₂,RingHom.ext_int (j.comp _) (Int.castRingHom ℂ),map_zero,← eval_map,hx]
    change (W.map (Int.castRingHom ℂ)).IsRoot (c t)
    rw [hw,prod_root_iff]
    exact ⟨t,rfl⟩
  have hi := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have hV : 0<V := by dsimp [V,wordBound]; positivity
  have ⟨hpos,hbad⟩ := bad_bound W c hw V hV hc
  obtain ⟨he,p,hp,hprime,havoid,z,hz⟩ := bounded_factor_prime method W g c hw (minpoly.monic hi)
    (minpoly.natDegree_pos hi) (minpoly.isIntegrallyClosed_dvd hi hv) V (B*(bad W).natAbs)
    (Nat.mul_pos hB hpos) hc
  let : Fact p.Prime := ⟨hprime⟩
  have : Nonempty (Word d) := ⟨t⟩
  have hmon : W.Monic := (Function.Injective.monic_map_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr
    (hw ▸ monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have hdeg : 0 < W.natDegree := by
    rw [← hmon.natDegree_map (Int.castRingHom ℂ),hw]
    simpa using (Fintype.card_pos : 0 < Fintype.card (Word d))
  have hs := separable_at_good_prime W (Nat.ne_of_gt hdeg) p (fun e => havoid (dvd_mul_of_dvd_right e B))
  exact ⟨g.natDegree,he,p,hp.trans (method.mono _ _ (Nat.mul_le_mul_left _ hbad)),hprime,
    fun e => havoid (dvd_mul_of_dvd_left e _),chosen_word_reduction d f (fun i => a i) hf M t hs z hz⟩

#print axioms chosen_prime_with

#print axioms bounded_factor_prime

end Erdos478.EffectiveResolvent
