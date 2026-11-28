import Erdos478RootWordPolynomial
import Erdos478EffectiveSplitting

/-!
# An elementary bound for simultaneous prime roots

Choose a weight separating all characteristic-zero root words. At a
prime preserving separability, a fixed word fixes one root in each
coordinate. A bounded Schur prime for the word polynomial realizes this
criterion while avoiding a supplied exceptional integer.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

/-- A fixed simple root of the word polynomial chooses a fixed entry
from each input factor. -/
theorem fixed_word {K : Type*} [Field K] {n : ℕ} (d : Fin n → ℕ) (a : (i : Fin n) → Fin (d i) → K)
    (φ : K →+* K) (M : ℕ)
    (closed : ∀ i j, ∃ l, φ (a i j) = a i l)
    (inj : Function.Injective (fun t : Word d => wordValue (M:K) (fun i => a i (t i))))
    (t : Word d) (ht : φ (wordValue (M:K) (fun i => a i (t i))) = wordValue (M:K) (fun i => a i (t i))) :
    ∀ i, φ (a i (t i)) = a i (t i) := by
  classical
  choose t' he using fun i => closed i (t i)
  have hw : φ (wordValue (M:K) (fun i => a i (t i))) =
      wordValue (M:K) (fun i => a i (t' i)) := by simp [wordValue,he]
  have hc := inj (hw.symm.trans ht)
  simpa only [hc] using he

private theorem ofFn_word {K : Type*} [Field K] [DecidableEq K] {n : ℕ} (x : Fin n → K) (M : K) :
    (Polynomial.ofFn n x).eval M = wordValue M x := by
  simp [Polynomial.ofFn_eq_sum_monomial,eval_finsetSum,wordValue,mul_comm]

/-- A bounded integer separates a family of words if its coordinate lists are distinct. -/
theorem word_separator {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 0<n)
    (d : Fin n → ℕ) (a : (i : Fin n) → Fin (d i) ↪ K) :
    ∃ M ≤ n*(Fintype.card (Word d))^2, Function.Injective
      (fun t : Word d => wordValue (M:K) (fun i => a i (t i))) := by
  classical
  let e : Word d ↪ (Fin n → K) := ⟨fun t i => a i (t i),
    fun _ _ h => funext fun i => (a i).injective (congrFun h i)⟩
  obtain ⟨M,hM,hi⟩ := evaluation_separator hn e
  refine ⟨M,hM,?_⟩
  intro t u h
  apply hi
  change evaluation (fun i => a i (t i)) (M:K) = evaluation (fun i => a i (u i)) (M:K)
  simpa only [evaluation,ofFn_word] using h

private theorem isRoot_word_prod {K I : Type*} [Field K] [Fintype I] (a : I → K) (x : K) :
    (∏ i, (X-C (a i))).IsRoot x ↔ ∃ i, x = a i := by
  classical
  simp [IsRoot.def,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

theorem roots_from_word {n : ℕ} (f : Fin n → ℤ[X]) (d : Fin n → ℕ)
    (hm : ∀ i, (f i).Monic) (hd : ∀ i, (f i).natDegree = d i)
    (M p : ℕ) [Fact p.Prime] (hs : ∀ i, ((f i).map (Int.castRingHom (ZMod p))).Separable)
    (hW : ((wordPolynomial n f d (M:ℤ)).map (Int.castRingHom (ZMod p))).Separable)
    (hroot : ∃ z : ZMod p, ((wordPolynomial n f d (M:ℤ)).map (Int.castRingHom (ZMod p))).IsRoot z) :
    ∀ i, ∃ z : ZMod p, ((f i).map (Int.castRingHom (ZMod p))).IsRoot z := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let j := algebraMap (ZMod p) K
  have lift (P : ℤ[X]) : (P.map (Int.castRingHom (ZMod p))).map j = P.map (Int.castRingHom K) := by
    rw [Polynomial.map_map,RingHom.ext_int (j.comp _) (Int.castRingHom K)]
  have hx (i) := enumerate_roots ((f i).map (Int.castRingHom K)) ((hm i).map _) (IsAlgClosed.splits _)
    (lift _ ▸ (hs i).map (f := j)) (((hm i).natDegree_map _).trans (hd i))
  choose a ha using hx
  let W := wordPolynomial n f d (M:ℤ)
  have hw : W.map (Int.castRingHom K) =
      ∏ t : Word d, (X-C (wordValue (M:K) (fun i => a i (t i)))) := by
    rw [show W = wordPolynomial n f d (M:ℤ) from rfl,wordPolynomial_map]
    simp_rw [ha]
    simpa using wordPolynomial_factors d (fun i => a i) (M:K)
  have hsep : (W.map (Int.castRingHom K)).Separable := lift W ▸ hW.map (f := j)
  obtain ⟨z,hz⟩ := hroot
  have hh : (W.map (Int.castRingHom K)).IsRoot (j z) := lift W ▸ hz.map (f := j)
  rw [hw] at hh hsep
  obtain ⟨t,ht⟩ := (isRoot_word_prod _ _).mp hh
  let φ := frobenius K p
  have hfixed : φ (j z) = j z := by rw [frobenius_def,← map_pow,ZMod.pow_card]
  have hat (i l) : ((f i).map (Int.castRingHom K)).IsRoot (a i l) := by
    rw [ha,isRoot_word_prod]
    exact ⟨l,rfl⟩
  have htuple := fixed_word d (fun i => a i) φ M (fun i l => by
    have hl := (hat i l).map (f := φ)
    rw [Polynomial.map_map,RingHom.ext_int (φ.comp _) (Int.castRingHom K),ha,isRoot_word_prod] at hl
    exact hl) hsep.injective_of_prod_X_sub_C t (ht ▸ hfixed)
  intro i
  have hp : (a i (t i))^p = a i (t i) := htuple i
  obtain ⟨m,he⟩ := (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr hp)
  refine ⟨(m : ZMod p),IsRoot.of_map (f := j) ?_ j.injective⟩
  rw [lift,show j (m : ZMod p) = a i (t i) by simpa [j] using he]
  exact hat i (t i)

def wordBound (n D U : ℕ) := n*U*(n*D^2+1)^n

theorem joint_prime {n : ℕ} (hn : 0<n) (d : Fin n → ℕ) (hd : ∀ i, 0<d i)
    (f : Fin n → ℤ[X]) (a : (i : Fin n) → Fin (d i) ↪ ℂ)
    (hf : ∀ i, (f i).map (Int.castRingHom ℂ) = ∏ j, (X-C (a i j)))
    (U B : ℕ) (hU : 0<U) (hB : 0<B) (hr : ∀ i j, ‖a i j‖ ≤ U)
    (safe : ∀ (p : ℕ) [Fact p.Prime], ¬p ∣ B → ∀ i, ((f i).map (Int.castRingHom (ZMod p))).Separable) :
    let D := Fintype.card (Word d)
    let V := wordBound n D U
    ∃ p ≤ schurBound D V (B*(2*V)^(D^2)), p.Prime ∧ ¬p ∣ B ∧
      ∀ i, ∃ z : ZMod p, ((f i).map (Int.castRingHom (ZMod p))).IsRoot z := by
  classical
  let D := Fintype.card (Word d)
  let V := wordBound n D U
  have : Nonempty (Word d) := ⟨fun i => ⟨0,hd i⟩⟩
  have hD : 0<D := Fintype.card_pos
  have hV : 0<V := by dsimp [V,wordBound]; positivity
  have hm (i) : (f i).Monic := (Function.Injective.monic_map_iff (f := Int.castRingHom ℂ)
    (by exact Int.cast_injective)).mpr (by rw [hf]; exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have hdeg (i) : (f i).natDegree = d i := by rw [← (hm i).natDegree_map (Int.castRingHom ℂ),hf]; simp
  obtain ⟨M,hM,hi⟩ := word_separator hn d a
  let c : Word d ↪ ℂ := ⟨fun t => wordValue (M:ℂ) (fun i => a i (t i)),hi⟩
  let W := wordPolynomial n f d (M:ℤ)
  have hw : W.map (Int.castRingHom ℂ) = ∏ t, (X-C (c t)) := by
    rw [show W = wordPolynomial n f d (M:ℤ) from rfl,wordPolynomial_map]
    simp_rw [hf]
    simpa [c] using wordPolynomial_factors d (fun i => a i) (M:ℂ)
  have hc (t : Word d) : ‖c t‖ ≤ V := by
    have hx := tag_norm (fun i => a i (t i)) (fun i => hr i (t i)) (M := M) (Equiv.refl _)
    have he : ‖c t‖ ≤ (n*U*(M+1)^n : ℕ) := by
      simpa [c,tag,ofFn_word,Function.comp_def] using hx
    refine he.trans ?_
    exact_mod_cast (by dsimp [V,wordBound,D]; gcongr : n*U*(M+1)^n ≤ V)
  have hmon : W.Monic := (Function.Injective.monic_map_iff (f := Int.castRingHom ℂ)
    (by exact Int.cast_injective)).mpr (by rw [hw]; exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have hwd : W.natDegree = D := by rw [← hmon.natDegree_map (Int.castRingHom ℂ),hw]; simp [D]
  obtain ⟨hb₁,hb₂⟩ := bad_bound W c hw V hV hc
  obtain ⟨p,hp,hprime,ha,hroot⟩ := bounded_prime_root W c hw V (B*(bad W).natAbs) (Nat.mul_pos hB hb₁) hc
  let : Fact p.Prime := ⟨hprime⟩
  have havoid : ¬p ∣ B := fun he => ha (dvd_mul_of_dvd_left he _)
  have hsep := separable_at_good_prime W (by omega) p (fun he => ha (dvd_mul_of_dvd_right he _))
  refine ⟨p,hp.trans ?_,hprime,havoid,roots_from_word f d hm hdeg M p (safe p havoid) hsep hroot⟩
  dsimp [schurBound,V,D]
  gcongr

#print axioms word_separator
#print axioms roots_from_word
#print axioms joint_prime

end Erdos478.EffectiveResolvent
